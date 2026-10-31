"""Random families whose sort may be ``Prop``, elaborated by Lean.

The kernel decides whether a recursor eliminates into every universe or only
into ``Prop`` (``elim_only_at_universe_zero``): a sort that is never zero
eliminates everywhere; a mutual block, or more than one constructor, only
into ``Prop``; one constructor everywhere exactly when each field is a proof
or an index of its result.  "Never zero" is a level question, so the sorts
here include ``Sort u``, ``imax`` and ``max`` forms, with parameters, Bool/
Nat/Prop/universe-valued indices, proof, data, equation and recursive
fields, and mutual blocks declared through ``variable``.  Lean's elaborator
refuses ``Sort u`` families outright; ``bootstrap.inductiveCheckResultingUniverse``
lifts that so the kernel decides.  Every checker must derive the recursor
Lean exported; there is no theorem, so there are no rejects.
"""

from __future__ import annotations

import copy
import json
import os
import random
import re
import subprocess
import tempfile
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

from .indgen import Generated, _lean_prefix
from .ndjson import Document
from .rewrite import _name_strings, share

SORTS = (
    "Prop", "Prop", "Prop", "Sort u", "Sort u", "Sort (imax u v)", "Sort (max u v)", "Sort (imax v u)",
    "Sort (max 1 u)", "Sort (imax 1 u)", "Sort (imax u 0)", "Sort (max u 0)", "Sort (u + 1)",
    "Sort (imax (u + 1) v)", "Sort (max 0 u)",
)
PARAMS = (("α", "Sort u"), ("β", "Sort v"), ("p", "Prop"), ("γ", "Type"), ("n", "Nat"))
INDICES = ("Nat", "Bool", "Prop", "α", "Sort u")
TWIN = "PestycydTwin"


class Family:
    def __init__(self, rng: random.Random, name: str, boundary: bool = False) -> None:
        """``boundary`` favours what Lean only eliminates into ``Prop``
        (single types, two constructors, data fields): forged recursors."""
        self.rng, self.name, self.boundary = rng, name, boundary
        self.mutual = not boundary and rng.random() < 0.3
        self.sort = rng.choice(SORTS)
        self.params = rng.sample(PARAMS, rng.choice((0, 1, 1, 2, 3)))
        self.names = {param for param, _ in self.params}
        pool = [index for index in INDICES if index != "α" or "α" in self.names]
        self.types = [f"T{i}" for i in range(rng.choice((2, 2, 3)) if self.mutual else 1)]
        self.indices = {t: [rng.choice(pool) for _ in range(rng.choice((0, 0, 1, 1, 2)))] for t in self.types}
        self.ctors = {t: self._ctors(t) for t in self.types}

    def applied(self, t: str, values: list[str]) -> str:
        # Inside a mutual block declared through `variable`, parameters are implicit.
        params = [] if self.mutual else [param for param, _ in self.params]
        return " ".join([t, *params, *values])

    def value(self, ty: str, fields: list[tuple[str, str]]) -> str | None:
        """A term of index type ``ty``: often a field of that type."""
        candidates = [field for field, field_type in fields if field_type == ty]
        if candidates and self.rng.random() < 0.6:
            return self.rng.choice(candidates)
        if ty == "Nat":
            return self.rng.choice(("0", "1", "(n + 1)" if "n" in self.names else "2"))
        if ty == "Bool":
            return self.rng.choice(("true", "false"))
        if ty == "Prop":
            return self.rng.choice(("True", "False", "p" if "p" in self.names else "True"))
        if ty == "Sort u":
            return self.rng.choice(candidates) if candidates else "PUnit"
        return None  # α: only a field can supply one

    def field_type(self, fields: list[tuple[str, str]]) -> str | None:
        kind = self.rng.choice(("proof", "data", "data", "data", "rec") if self.boundary else ("proof", "data", "data", "rec", "eq"))
        if kind == "proof":
            return self.rng.choice(("True", "p" if "p" in self.names else "True", "1 = 1"))
        if kind == "data":
            return self.rng.choice(["Nat", "Bool", "Prop", *(param for param, ty in self.params if ty != "Nat")])
        if kind == "eq" and fields:
            field, _ = self.rng.choice(fields)
            return f"{field} = {field}"
        target = self.rng.choice(self.types)
        values = [self.value(index, fields) for index in self.indices[target]]
        return None if None in values else self.applied(target, values)  # type: ignore[arg-type]

    def _ctors(self, t: str) -> list[str]:
        """Constructor types, as Lean text over the block's type names."""
        ctors = []
        for _ in range(self.rng.choice((1, 2, 2) if self.boundary else (0, 1, 1, 1, 2))):
            fields: list[tuple[str, str]] = []
            for j in range(self.rng.choice((0, 1, 2, 3))):
                ty = self.field_type(fields)
                if ty is not None:
                    fields.append((f"x{j}", ty))
            values = [self.value(index, fields) for index in self.indices[t]]
            if None not in values:
                parts = [f"({field} : {ty})" for field, ty in fields]
                ctors.append(" → ".join([*parts, self.applied(t, values)]))  # type: ignore[list-item]
        return ctors

    def binders(self) -> str:
        return "".join(f" ({param} : {ty})" for param, ty in self.params)

    def declaration(self, t: str, name: str | None = None, sort: str | None = None) -> str:
        """``t``'s declaration, optionally renamed (with its self-references)
        and in another sort."""
        arity = " → ".join([*self.indices[t], sort or self.sort])
        lines = [f"inductive {t}{'' if self.mutual else self.binders()} : {arity} where"]
        lines += [f"  | c{number} : {ctor}" for number, ctor in enumerate(self.ctors[t])]
        text = "\n".join(lines)
        return re.sub(rf"\b{t}\b", name, text) if name else text

    def source(self, forge: bool = False) -> str:
        body = "\n".join(self.declaration(t) for t in self.types)
        if self.mutual:
            variables = f"variable{self.binders()}\n" if self.params else ""
            body = f"section\n{variables}mutual\n{body}\nend\nend"
        if forge:
            body += f"\n\n{self.declaration('T0', TWIN, self.twin_sort())}\n\n{self.use()}"
        return (
            "universe u v\n\nset_option bootstrap.inductiveCheckResultingUniverse false\n\n"
            f"namespace {self.name}\n\n{body}\n\nend {self.name}\n"
        )

    # ---- forged eliminators (single types only)
    def twin_sort(self) -> str:
        """A sort over the same universes that is never zero."""
        level = "0" if self.sort == "Prop" else self.sort.removeprefix("Sort ")
        return f"Sort (max 1 {level})"

    def use(self) -> str:
        """``use : T params indices → Type`` through the twin's large recursor."""
        indices = self.indices["T0"]
        names = [f"i{k}" for k in range(len(indices))]
        index_binders = "".join(f" {{{n} : {ty}}}" for n, ty in zip(names, indices))
        major = " ".join([TWIN, *(param for param, _ in self.params), *names])
        motive = "fun " + " ".join(["_"] * (len(indices) + 1)) + " => Type"
        minors = " ".join(["(by intros; exact Nat)"] * len(self.ctors["T0"]))
        return (
            f"def use{self.binders()}{index_binders} (t : {major}) : Type :=\n"
            f"  {TWIN}.rec (motive := {motive}) {minors} t"
        )


def forge(export: str, namespace: str) -> tuple[str, str, bool] | None:
    """Split an export of ``T0``, its twin and ``use`` into the honest
    export of ``T0`` and the forged one, where the twin's large recursor and
    ``use`` are renamed onto ``T0``; also whether Lean gave ``T0`` itself a
    large eliminator (then the forged recursor is the real one)."""
    lines = [json.loads(line) for line in export.splitlines() if line.strip()]
    names = _name_strings(lines)
    ids = {text: number for number, text in names.items()}
    blocks = {names[line["inductive"]["types"][0]["name"]]: index
              for index, line in enumerate(lines) if "inductive" in line}
    t_name, twin_name = f"{namespace}.T0", f"{namespace}.{TWIN}"
    if t_name not in blocks or twin_name not in blocks:
        return None
    t_index, twin_index = blocks[t_name], blocks[twin_name]
    t_block, twin_block = lines[t_index]["inductive"], lines[twin_index]["inductive"]
    if t_block["types"][0]["levelParams"] != twin_block["types"][0]["levelParams"]:
        return None
    t_rec = t_block["recs"][0]
    large = len(t_rec["levelParams"]) > len(t_block["types"][0]["levelParams"])
    use = [index for index, line in enumerate(lines) if "def" in line and names[line["def"]["name"]].endswith(".use")]
    honest = [line for index, line in enumerate(lines) if index not in {twin_index, *use}]

    renamed = {ids[twin_name]: ids[t_name], twin_block["recs"][0]["name"]: t_rec["name"]}
    for twin_ctor, t_ctor in zip(twin_block["ctors"], t_block["ctors"]):
        renamed[twin_ctor["name"]] = t_ctor["name"]
    forged_lines = copy.deepcopy(lines)
    for line in forged_lines:
        const = line.get("const")
        if isinstance(const, dict) and const.get("name") in renamed:
            const["name"] = renamed[const["name"]]
    rec = copy.deepcopy(twin_block["recs"][0])
    # K-like elimination is a property of T0 (a proposition), not of its twin.
    rec["name"], rec["all"], rec["k"] = t_rec["name"], [ids[t_name]], t_rec["k"]
    for rule in rec["rules"]:
        rule["ctor"] = renamed[rule["ctor"]]
    block = copy.deepcopy(t_block)
    block["recs"] = [rec]
    # The twin's recursor references records emitted after T0's block.
    forged_lines[twin_index] = {"inductive": block}
    del forged_lines[t_index]
    shared = share(Document(tuple(forged_lines)))
    if shared is None:
        return None
    return Document(tuple(honest)).render(), shared.render(), large


def elaborate(family: Family, lean: str, leanexport: str, prefix: str, forged: bool = False) -> Generated:
    forged = forged and not family.mutual
    text = family.source(forge=forged)
    with tempfile.TemporaryDirectory(prefix="pestycyd-propgen-") as directory:
        module = Path(directory) / f"{family.name}.lean"
        module.write_text(text)
        compiled = subprocess.run(
            [lean, "-o", str(module.with_suffix(".olean")), str(module)],
            capture_output=True, text=True, cwd=directory, timeout=120,
        )
        if compiled.returncode != 0:
            output = (compiled.stdout + compiled.stderr).strip()
            return Generated(family.name, text, None, output.splitlines()[0] if output else "lean failed")
        names = [f"{family.name}.T0", *([f"{family.name}.use"] if forged else [])]
        exported = subprocess.run(
            [leanexport, family.name, "--", *names],
            capture_output=True, text=True, cwd=directory, timeout=120,
            env={**os.environ, "LEAN_PATH": f"{directory}:{prefix}/lib/lean"},
        )
        if exported.returncode != 0:
            return Generated(family.name, text, None, f"leanexport: {exported.stderr.strip()[:200]}")
    if not forged:
        return Generated(family.name, text, exported.stdout)
    split = forge(exported.stdout, family.name)
    if split is None:
        return Generated(family.name, text, None, "forge: twin does not mirror T0")
    honest, forged_text, large = split
    return Generated(family.name, text, honest, forged=forged_text, forged_valid=large)


def generate(
    count: int, seed: int, lean: str = "lean", leanexport: str = "leanexport", workers: int | None = None,
    forged: bool = False,
) -> list[Generated]:
    rng = random.Random(seed)
    families = [Family(rng, f"PestycydProp{seed}x{number}", boundary=forged) for number in range(count)]
    prefix = _lean_prefix(lean)
    with ThreadPoolExecutor(max_workers=workers or os.cpu_count() or 4) as pool:
        return list(pool.map(lambda family: elaborate(family, lean, leanexport, prefix, forged), families))
