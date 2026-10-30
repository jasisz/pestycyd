"""Random inductive families, elaborated by Lean and exported as seeds.

Mutating existing exports only reshuffles the shapes their authors wrote.
This module invents new ones: random parameters, indices, universe levels,
constructor fields (plain, recursive, reflexive, nested through ``List``)
and a closed term of the type.  Each family comes with a theorem

    @T.rec params motives minors indices term = N := rfl

whose minors compute ``ctor number + 1 + Σ recursive results``; Python evaluates
the same fold, so ``N`` is known independently of every checker.  The fold
is positive and offset by ``OFFSET`` so that ``N`` is the only literal of
its value in the export (an export shares equal literals in one record): bumping that one record gives a document every checker must
reject (``shifted``).  Lean is
the validity filter: a family it refuses (positivity, universes, large
elimination) is dropped, the rest are exported with ``leanexport``.
Propositional families whose recursor only eliminates into ``Prop`` are
used with a ``True``-valued motive instead.
"""

from __future__ import annotations

import json
import os
import random
import subprocess
import tempfile
from concurrent.futures import ThreadPoolExecutor
from dataclasses import dataclass, field
from pathlib import Path

from .ndjson import Document

OFFSET = 1_000_000
INDEX_TYPES = {"Bool": ("true", "false"), "Unit": ("()",)}
PARAM_KINDS = ("Type", "Prop")
SORTS = ("Type", "Prop", "Type u", "Sort (max 1 u)")


@dataclass(frozen=True)
class Field:
    """``kind`` is bool, nat, param, rec, refl or nested; ``at`` holds the
    index values of a recursive field and ``param`` the parameter number."""

    kind: str
    at: tuple[str, ...] = ()
    param: int = 0


@dataclass(frozen=True)
class Ctor:
    fields: tuple[Field, ...]
    # Result indices: a constant, or "#j" for the value of field j.
    result: tuple[str, ...]


@dataclass(frozen=True)
class Family:
    name: str
    sort: str
    params: tuple[str, ...]
    indices: tuple[str, ...]
    ctors: tuple[Ctor, ...]

    @property
    def universe(self) -> bool:
        return "u" in self.sort

    @property
    def nested(self) -> tuple[tuple[str, ...], ...]:
        """Distinct ``List (T idx)`` occurrences; each gets its own motive."""
        seen: list[tuple[str, ...]] = []
        for ctor in self.ctors:
            for item in ctor.fields:
                if item.kind == "nested" and item.at not in seen:
                    seen.append(item.at)
        return tuple(seen)


@dataclass
class Value:
    """A closed constructor term, its indices and its fold result."""

    lean: str
    at: tuple[str, ...]
    fold: int
    depth: int = 0
    children: list["Value"] = field(default_factory=list)


def random_family(rng: random.Random, name: str) -> Family:
    sort = rng.choice(SORTS)
    params = tuple(rng.choice(PARAM_KINDS) for _ in range(rng.choice((0, 1, 1, 2))))
    indices = tuple(rng.choice(tuple(INDEX_TYPES)) for _ in range(rng.choice((0, 1, 1, 2))))
    ctors = []
    for number in range(rng.choice((1, 2, 2, 3, 4))):
        fields: list[Field] = []
        for _ in range(rng.choice((0, 1, 2, 2, 3))):
            choices = ["bool", "nat"]
            choices += ["param"] * bool(params)
            if number > 0:  # the first constructor stays a base case
                choices += ["rec", "rec", "refl"]
                if sort != "Prop":
                    choices.append("nested")
            kind = rng.choice(choices)
            at = tuple(rng.choice(INDEX_TYPES[index]) for index in indices)
            fields.append(Field(kind, at if kind in {"rec", "refl", "nested"} else (), rng.randrange(max(1, len(params)))))
        result = []
        for index in indices:
            refs = [f"#{j}" for j, f in enumerate(fields) if f.kind == "bool" and index == "Bool"]
            result.append(rng.choice(refs) if refs and rng.random() < 0.4 else rng.choice(INDEX_TYPES[index]))
        ctors.append(Ctor(tuple(fields), tuple(result)))
    return Family(name, sort, params, indices, tuple(ctors))


def _param_names(family: Family) -> list[str]:
    return [f"α{i}" for i in range(len(family.params))]


def _param_type(family: Family, kind: str) -> str:
    if kind == "Prop":
        return "Prop"
    return "Type u" if family.universe and family.sort == "Type u" else ("Sort u" if family.universe else "Type")


def _applied(family: Family, at: tuple[str, ...]) -> str:
    return " ".join(["T", *_param_names(family), *at])


def _field_type(family: Family, item: Field) -> str:
    if item.kind == "bool":
        return "Bool"
    if item.kind == "nat":
        return "Nat"
    if item.kind == "param":
        return _param_names(family)[item.param]
    target = _applied(family, item.at)
    if item.kind == "rec":
        return target
    if item.kind == "refl":
        return f"Bool → {target}"
    return f"List ({target})"


def declaration(family: Family) -> str:
    binders = "".join(f" ({n} : {_param_type(family, k)})" for n, k in zip(_param_names(family), family.params))
    arity = " → ".join([*family.indices, family.sort])
    lines = [f"inductive T{binders} : {arity} where"]
    for number, ctor in enumerate(family.ctors):
        parts = [f"(x{j} : {_field_type(family, item)})" for j, item in enumerate(ctor.fields)]
        result = [f"x{value[1:]}" if value.startswith("#") else value for value in ctor.result]
        lines.append(f"  | c{number} : {' → '.join([*parts, _applied(family, tuple(result))])}")
    return "\n".join(lines)


def _instances(family: Family) -> list[str]:
    return ["True" if kind == "Prop" else "Bool" for kind in family.params]


def _plain(rng: random.Random, family: Family, item: Field) -> str:
    if item.kind == "bool":
        return rng.choice(("true", "false"))
    if item.kind == "nat":
        return str(rng.choice((0, 1, 7, 300)))
    return "trivial" if family.params[item.param] == "Prop" else rng.choice(("true", "false"))


def build_values(rng: random.Random, family: Family, rounds: int = 12) -> list[Value]:
    """Closed terms bottom-up; a constructor fires once its recursive
    fields can be filled with already-built values of the right indices."""
    values: list[Value] = []
    for _ in range(rounds):
        number = rng.randrange(len(family.ctors))
        ctor = family.ctors[number]
        args: list[str] = []
        chosen: dict[int, str] = {}
        fold, depth, children = number + 1, 0, []
        ok = True
        for j, item in enumerate(ctor.fields):
            if item.kind in {"bool", "nat", "param"}:
                text = _plain(rng, family, item)
                chosen[j] = text
                args.append(text)
                continue
            pool = [value for value in values if value.at == item.at]
            if item.kind == "nested":
                picked = rng.sample(pool, k=min(len(pool), rng.choice((0, 1, 2))))
                args.append("[" + ", ".join(value.lean for value in picked) + "]")
                fold += sum(value.fold for value in picked)
                depth = max([depth, *(value.depth + 1 for value in picked)])
                children += picked
                continue
            if not pool:
                ok = False
                break
            child = rng.choice(pool[-4:])
            args.append(f"({child.lean})" if item.kind == "rec" else f"(fun _ => {child.lean})")
            fold += child.fold
            depth = max(depth, child.depth + 1)
            children.append(child)
        if not ok:
            continue
        at = tuple(chosen[int(value[1:])] if value.startswith("#") else value for value in ctor.result)
        head = f"T.c{number}"
        lean = " ".join([head, *args]) if args else head
        values.append(Value(lean, at, fold, depth, children))
    return values


def _minor(family: Family, number: int, ctor: Ctor, prop: bool) -> str:
    binders = ["_"] * len(ctor.fields)
    terms = []
    for j, item in enumerate(ctor.fields):
        if item.kind in {"rec", "refl", "nested"}:
            binders.append(f"ih{j}")
            terms.append(f"(ih{j} true)" if item.kind == "refl" else f"ih{j}")
    body = "trivial" if prop else _sum([str(number + 1), *terms])
    return f"(fun {' '.join(binders)} => {body})" if binders else f"({body})"


def _sum(terms: list[str]) -> str:
    return terms[0] if len(terms) == 1 else f"Nat.add {terms[0]} ({_sum(terms[1:])})"


def use_theorem(family: Family, major: Value, prop: bool) -> str:
    instances = _instances(family)
    motive_binders = " ".join(["_"] * (len(family.indices) + 1))
    target = "True" if prop else "Nat"
    motives = [f"(fun {motive_binders} => {target})"]
    minors = [_minor(family, number, ctor, prop) for number, ctor in enumerate(family.ctors)]
    for _ in family.nested:
        motives.append(f"(fun _ => {target})")
        minors += [f"({'trivial' if prop else '0'})", f"(fun _ _ a b => {'trivial' if prop else 'Nat.add a b'})"]
    application = " ".join(["@T.rec", *instances, *motives, *minors, *major.at, f"({major.lean})"])
    if prop:
        return f"theorem use : {application} = trivial := rfl"
    return f"theorem use : Nat.add {OFFSET} ({application}) = {OFFSET + major.fold} := rfl"


def source(family: Family, major: Value, prop: bool) -> str:
    universe = "universe u\n\n" if family.universe else ""
    return (
        f"{universe}namespace {family.name}\n\n{declaration(family)}\n\n"
        f"{use_theorem(family, major, prop)}\n\nend {family.name}\n"
    )


@dataclass(frozen=True)
class Generated:
    name: str
    lean: str
    export: str | None
    error: str = ""
    fold: int | None = None  # None for the True-motive (Prop) form

    def shifted(self) -> str | None:
        """The export with the theorem's result literal off by one."""
        if self.export is None or self.fold is None:
            return None
        target = str(OFFSET + self.fold)
        lines = [json.loads(line) for line in self.export.splitlines() if line.strip()]
        hits = [line for line in lines if line.get("natVal") == target]
        if len(hits) != 1:
            return None
        hits[0]["natVal"] = str(OFFSET + self.fold + 1)
        return Document(tuple(lines)).render()


def _lean_prefix(lean: str) -> str:
    return subprocess.run([lean, "--print-prefix"], capture_output=True, text=True, check=True).stdout.strip()


def elaborate(family: Family, major: Value, lean: str, leanexport: str, prefix: str) -> Generated:
    """Compile with a Nat motive, falling back to True for Prop-only elimination."""
    error = ""
    for prop in (False, True) if family.sort == "Prop" else (False,):
        text = source(family, major, prop)
        with tempfile.TemporaryDirectory(prefix="pestycyd-indgen-") as directory:
            module = Path(directory) / f"{family.name}.lean"
            module.write_text(text)
            compiled = subprocess.run(
                [lean, "-o", str(module.with_suffix(".olean")), str(module)],
                capture_output=True, text=True, cwd=directory, timeout=120,
            )
            if compiled.returncode != 0:
                output = (compiled.stdout + compiled.stderr).strip()
                error = output.splitlines()[0] if output else "lean failed"
                continue
            exported = subprocess.run(
                [leanexport, family.name, "--", f"{family.name}.use"],
                capture_output=True, text=True, cwd=directory, timeout=120,
                env={**os.environ, "LEAN_PATH": f"{directory}:{prefix}/lib/lean"},
            )
            if exported.returncode != 0:
                return Generated(family.name, text, None, f"leanexport: {exported.stderr.strip()[:200]}")
            return Generated(family.name, text, exported.stdout, fold=None if prop else major.fold)
    return Generated(family.name, source(family, major, False), None, error)


def generate(
    count: int, seed: int, lean: str = "lean", leanexport: str = "leanexport", workers: int | None = None
) -> list[Generated]:
    rng = random.Random(seed)
    jobs: list[tuple[Family, Value]] = []
    attempts = 0
    while len(jobs) < count and attempts < count * 20:
        attempts += 1
        family = random_family(rng, f"PestycydGen{seed}x{attempts}")
        values = build_values(rng, family)
        if values:
            jobs.append((family, max(values, key=lambda value: (value.depth, value.fold))))
    prefix = _lean_prefix(lean)
    with ThreadPoolExecutor(max_workers=workers or os.cpu_count() or 4) as pool:
        return list(pool.map(lambda job: elaborate(*job, lean, leanexport, prefix), jobs))
