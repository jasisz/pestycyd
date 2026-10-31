"""Random mutual blocks of deeply nested inductives, measured with ``sizeOf``.

``indgen`` writes the recursor application by hand, which limits it to one
type nested through ``List``.  Here the blocks hold one to three mutual
types, optionally indexed by ``Bool``, whose fields nest the block through
``List``, ``Option``, ``×``, ``Array``, ``ULift``, ``Subtype``, a ``Σ``
over ``Vec`` (the nested occurrence under a binder, indexed by the bound
variable) and four containers declared in the module: ``Rose`` (itself
nested), ``Pair2`` (a structure over ``List``), ``Vec`` (indexed) and
``Wrap`` (reflexive), plus the mutual pair ``EL``/``OL``, up to three
containers deep.
Lean derives ``SizeOf`` for the block through its recursors, one motive per
nested auxiliary type, so

    Nat.add OFFSET (sizeOf v) = OFFSET + N := rfl

drives a checker through every auxiliary recursor at once.  ``N`` comes
from ``#reduce`` (the elaborator's whnf, not the kernel); the theorem is then
compiled, so Lean's kernel confirms it before the module is exported.  A
second theorem ``fold`` evaluates structurally recursive functions over the
block (one per block type and nested container type), compiled by Lean
through ``brecOn``/``below``.  Some blocks live in ``Type u``.
"""

from __future__ import annotations

import os
import random
import re
import subprocess
import tempfile
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

from .indgen import OFFSET, Generated, _lean_prefix

FOLD_OFFSET = 2 * OFFSET

PRELUDE = {
    "Rose": "inductive Rose (α : Type u) where\n  | node : α → List (Rose α) → Rose α",
    "Pair2": "structure Pair2 (α : Type u) (β : Type u) where\n  fst : α\n  snd : List β",
    "Vec": "inductive Vec (α : Type u) : Nat → Type u where\n  | nil : Vec α 0\n  | cons : α → Vec α n → Vec α (n + 1)",
    "Wrap": "inductive Wrap (α : Type u) : Type u where\n  | none\n  | one : α → Wrap α\n  | many : (Bool → Wrap α) → Wrap α",
    # A mutual container: nesting through either member copies the whole block.
    "EL": "mutual\ninductive EL (α : Type u) where\n  | nil : EL α\n  | cons : α → OL α → EL α\n"
          "inductive OL (α : Type u) where\n  | cons : α → EL α → OL α\nend",
}
CONTAINERS = ("List", "Option", "Prod", "Array", "Rose", "Pair2", "Vec", "Wrap", "ULift", "Subtype", "Sigma", "EL", "OL")
# A field type is a tuple: ("bool",), ("nat",), ("ref", T, index|None),
# ("refl", ref) for Bool → ref, or (container, inner[, second]).
FieldType = tuple


class Block:
    def __init__(self, rng: random.Random, name: str) -> None:
        self.rng, self.name = rng, name
        self.types = [f"T{i}" for i in range(rng.choice((1, 2, 2, 3)))]
        self.indexed = {t: rng.random() < 0.4 for t in self.types}
        self.universe = rng.random() < 0.3
        self.used: set[str] = set()
        self.ctors = {t: self._ctors(t) for t in self.types}

    def _ref(self) -> FieldType:
        t = self.rng.choice(self.types)
        return ("ref", t, self.rng.choice(("true", "false")) if self.indexed[t] else None)

    def _field(self, depth: int, base: bool) -> FieldType:
        r = self.rng.random()
        if base or depth > 2 or r < 0.25:
            return self.rng.choice((("bool",), ("nat",)))
        if r < 0.45 and depth == 0:
            return self._ref()
        if r < 0.5 and depth == 0:
            return ("refl", self._ref())
        container = self.rng.choice(CONTAINERS)
        self.used.update({"Sigma": ("Vec",), "OL": ("EL",)}.get(container, (container,)))
        parts = [self._field(depth + 1, False) if self.rng.random() < 0.5 else self._ref()]
        if container in {"Prod", "Pair2"}:
            parts.append(self._field(depth + 1, False) if self.rng.random() < 0.5 else self._ref())
        return (container, *parts)

    def _ctors(self, t: str) -> list[tuple[list[FieldType], str | None]]:
        ctors = []
        for number in range(self.rng.choice((1, 2, 2, 3))):
            fields = [self._field(0, number == 0) for _ in range(self.rng.choice((0, 1, 2, 3)))]
            if number == 0 and self.rng.random() < 0.5:  # a container that may stay empty
                container = self.rng.choice(("List", "Option", "Array"))
                self.used.add(container)
                fields.append((container, self._ref()))
            ctors.append((fields, self.rng.choice(("true", "false")) if self.indexed[t] else None))
        return ctors

    def show(self, ty: FieldType, levels: bool = False, length: str = "2") -> str:
        """Lean syntax; ``levels`` spells the block's universe out (outside
        the block itself), ``length`` is the ``Vec`` index."""
        kind = ty[0]
        if kind == "bool":
            return "Bool"
        if kind == "nat":
            return "Nat"
        if kind == "ref":
            head = f"{ty[1]}.{{u}}" if levels and self.universe else ty[1]
            return f"{head} {ty[2]}" if ty[2] else head
        if kind == "refl":
            return f"Bool → {self.show(ty[1], levels)}"
        if kind == "Prod":
            return f"({self.show(ty[1], levels)} × {self.show(ty[2], levels)})"
        if kind == "Pair2":
            return f"(Pair2 ({self.show(ty[1], levels)}) ({self.show(ty[2], levels)}))"
        if kind == "Vec":
            return f"(Vec ({self.show(ty[1], levels)}) {length})"
        if kind == "Sigma":
            return f"(Σ n, Vec ({self.show(ty[1], levels)}) n)"
        if kind == "Subtype":
            return f"{{x : {self.show(ty[1], levels)} // True}}"
        if kind == "ULift":
            return f"(ULift.{{0}} ({self.show(ty[1], levels)}))"
        return f"({kind} ({self.show(ty[1], levels)}))"

    def declaration(self) -> str:
        lines = []
        for t in self.types:
            sort = "Type u" if self.universe else "Type"
            lines.append(f"inductive {t} : {'Bool → ' if self.indexed[t] else ''}{sort} where")
            for number, (fields, index) in enumerate(self.ctors[t]):
                parts = [f"(x{j} : {self.show(item)})" for j, item in enumerate(fields)]
                lines.append(f"  | c{number} : {' → '.join([*parts, f'{t} {index}' if index else t])}")
        body = "\n".join(lines)
        return f"mutual\n{body}\nend" if len(self.types) > 1 else body

    def term(self, ty: FieldType, pool: dict, depth: int = 0) -> str | None:
        kind, rng = ty[0], self.rng
        if kind == "bool":
            return rng.choice(("true", "false"))
        if kind == "nat":
            return str(rng.choice((0, 1, 5, 300)))
        if kind == "ref":
            candidates = pool.get((ty[1], ty[2]), [])
            return f"({rng.choice(candidates[-5:])})" if candidates else None
        if kind == "refl":
            value = self.term(ty[1], pool, depth)
            return f"(fun _ => {value})" if value else None
        if depth > 4:
            return None

        def sub(inner: FieldType) -> str | None:
            return self.term(inner, pool, depth + 1)

        def some(inner: FieldType, counts: tuple[int, ...]) -> list[str]:
            return [x for x in (sub(inner) for _ in range(rng.choice(counts))) if x]

        if kind in {"List", "Array"}:
            return ("#" if kind == "Array" else "") + "[" + ", ".join(some(ty[1], (0, 1, 2, 3))) + "]"
        if kind == "Option":
            value = sub(ty[1]) if rng.random() < 0.7 else None
            return f"(some {value})" if value else "none"
        first = sub(ty[1])
        if first is None:
            return "Wrap.none" if kind == "Wrap" else None
        if kind == "Prod":
            second = sub(ty[2])
            return f"({first}, {second})" if second else None
        if kind == "Pair2":
            return f"(Pair2.mk {first} [{', '.join(some(ty[2], (0, 1, 2)))}])"
        if kind == "Vec":
            second = sub(ty[1])
            return f"(Vec.cons {first} (Vec.cons {second} Vec.nil))" if second else None
        if kind == "Sigma":
            return f"⟨1, Vec.cons {first} Vec.nil⟩" if rng.random() < 0.8 else "⟨0, Vec.nil⟩"
        if kind == "Subtype":
            return f"⟨{first}, trivial⟩"
        if kind == "ULift":
            return f"(ULift.up {first})"
        if kind == "OL":
            return f"(OL.cons {first} EL.nil)"
        if kind == "EL":
            second = sub(ty[1]) if rng.random() < 0.6 else None
            return f"(EL.cons {first} (OL.cons {second} EL.nil))" if second else f"(EL.cons {first} (OL.cons {first} EL.nil))"
        if kind == "Rose":
            kids = [f"(Rose.node {x} [])" for x in some(ty[1], (0, 1, 2))]
            return f"(Rose.node {first} [{', '.join(kids)}])"
        r = rng.random()  # Wrap
        if r < 0.2:
            return "Wrap.none"
        return f"(Wrap.one {first})" if r < 0.6 else f"(Wrap.many (fun b => if b then Wrap.one {first} else Wrap.none))"

    def values(self, rounds: int = 30) -> list[tuple[str, str]]:
        """Closed terms bottom-up as (type, term), grouped by type and index."""
        pool: dict[tuple[str, str | None], list[str]] = {}
        for _ in range(rounds):
            t = self.rng.choice(self.types)
            number = self.rng.randrange(len(self.ctors[t]))
            fields, index = self.ctors[t][number]
            args = [self.term(item, pool) for item in fields]
            if all(arg is not None for arg in args):
                pool.setdefault((t, index), []).append(" ".join([f"{t}.c{number}", *args]))  # type: ignore[list-item]
        return [(self.show(("ref", *key), levels=True), value) for key, values in pool.items() for value in values]

    # ---- structural recursion: one function per block type and per nested
    # container type that mentions the block, all in one mutual group.
    def mentions(self, ty: FieldType) -> bool:
        if ty[0] in {"bool", "nat"}:
            return False
        return ty[0] in {"ref", "refl"} or any(self.mentions(part) for part in ty[1:])

    def fold_name(self, ty: FieldType, defs: dict[str, str]) -> str:
        """The function folding ``ty``, defining it (and its helpers) on first use."""
        key = ty[1] if ty[0] == "ref" else self.show(ty, length="n")
        if key in defs:
            return defs[key].split()[1]
        name = f"f{ty[1]}" if ty[0] == "ref" else f"h{len(defs)}"
        defs[key] = f"def {name} "  # reserve the name before recursing
        if ty[0] == "ref":
            t = ty[1]
            arms = []
            for number, (fields, _) in enumerate(self.ctors[t]):
                parts = [str(number + 1)] + [self.measure(item, f"x{j}", defs) for j, item in enumerate(fields)]
                binders = "".join(f" x{j}" for j in range(len(fields)))
                arms.append(f"  | {'_, ' if self.indexed[t] else ''}.c{number}{binders} => {' + '.join(parts)}")
            head = self.show(("ref", t, "b" if self.indexed[t] else None), levels=True)
            signature = f"{{b : Bool}} → {head}" if self.indexed[t] else head
        else:
            kind, inner = ty[0], ty[1]
            m = lambda item, var: self.measure(item, var, defs)  # noqa: E731
            signature = self.show(ty, levels=True, length="n")
            if kind not in {"Sigma", "Subtype"}:  # their brackets are syntax
                signature = signature[1:-1]
            if kind == "List":
                arms = ["  | [] => 0", f"  | x :: xs => 1 + {m(inner, 'x')} + {name} xs"]
            elif kind == "Option":
                arms = ["  | none => 0", f"  | some x => 1 + {m(inner, 'x')}"]
            elif kind == "Prod":
                arms = [f"  | (a, b) => {m(inner, 'a')} + {m(ty[2], 'b')}"]
            elif kind == "Array":
                arms = [f"  | ⟨xs⟩ => 1 + {m(('List', inner), 'xs')}"]
            elif kind == "Pair2":
                arms = [f"  | ⟨a, bs⟩ => {m(inner, 'a')} + {m(('List', ty[2]), 'bs')}"]
            elif kind == "Vec":
                signature = f"{{n : Nat}} → {signature}"
                arms = ["  | _, .nil => 0", f"  | _, .cons a v => 1 + {m(inner, 'a')} + {name} v"]
            elif kind == "Sigma":
                arms = [f"  | ⟨_, v⟩ => 1 + {m(('Vec', inner), 'v')}"]
            elif kind in {"Subtype", "ULift"}:
                pattern = "⟨a, _⟩" if kind == "Subtype" else "⟨a⟩"
                arms = [f"  | {pattern} => {m(inner, 'a')}"]
            elif kind == "OL":
                arms = [f"  | .cons a e => 1 + {m(inner, 'a')} + {m(('EL', inner), 'e')}"]
            elif kind == "EL":
                arms = ["  | .nil => 0", f"  | .cons a o => 1 + {m(inner, 'a')} + {m(('OL', inner), 'o')}"]
            elif kind == "Rose":
                arms = [f"  | .node a kids => 1 + {m(inner, 'a')} + {m(('List', ty), 'kids')}"]
            else:  # Wrap
                arms = ["  | .none => 0", f"  | .one a => {m(inner, 'a')}",
                        f"  | .many k => 1 + {name} (k true) + {name} (k false)"]
        defs[key] = "\n".join([f"def {name} : {signature} → Nat", *arms])
        return name

    def measure(self, ty: FieldType, var: str, defs: dict[str, str]) -> str:
        kind = ty[0]
        if kind == "bool":
            return f"(if {var} then 1 else 0)"
        if kind == "nat":
            return var
        if kind == "refl":
            return f"{self.fold_name(ty[1], defs)} ({var} true)"
        if not self.mentions(ty):
            return "1"
        return f"{self.fold_name(ty, defs)} {var}"

    def folds(self, top: str) -> tuple[str, str]:
        """The mutual fold group and the name of the function folding ``top``."""
        defs: dict[str, str] = {}
        name = self.fold_name(("ref", top, None), defs)
        for t in self.types:
            self.fold_name(("ref", t, None), defs)
        body = "\n".join(defs.values())
        return (f"mutual\n{body}\nend" if len(defs) > 1 else body), name

    def header(self) -> str:
        containers = "\n\n".join(text for name, text in PRELUDE.items() if name in self.used)
        return f"universe u\n\n{containers}\n\nnamespace {self.name}\n\n{self.declaration()}\n\n"


def pick_major(values: list[tuple[str, str]]) -> tuple[str, str]:
    major = max(values, key=lambda item: len(item[1]))
    if len(major[1]) <= 1500:
        return major
    return min(values, key=lambda item: abs(len(item[1]) - 600))


def _compile(directory: str, module: str, text: str, lean: str) -> subprocess.CompletedProcess[str]:
    path = Path(directory) / f"{module}.lean"
    path.write_text(text)
    return subprocess.run(
        [lean, "-o", str(path.with_suffix(".olean")), str(path)],
        capture_output=True, text=True, cwd=directory, timeout=300,
    )


def _first_line(result: subprocess.CompletedProcess[str]) -> str:
    output = (result.stdout + result.stderr).strip()
    return output.splitlines()[0] if output else "lean failed"


def elaborate(block: Block, major: tuple[str, str], lean: str, leanexport: str, prefix: str) -> Generated:
    """sizeOf theorem ``use`` plus, when Lean accepts the folds, ``fold``."""
    ty, term = major
    top = ty.split()[0].split(".")[0]
    folds, fold = block.folds(top)
    header, footer = block.header(), f"\nend {block.name}\n"
    value = f"(({term} : {ty}))"
    error = ""
    with tempfile.TemporaryDirectory(prefix="pestycyd-nestgen-") as directory:
        for with_folds in (True, False):
            body = header + (f"{folds}\n\n" if with_folds else "")
            probes = f"#reduce sizeOf {value}\n" + (f"#reduce {fold} {value}\n" if with_folds else "")
            probe = _compile(directory, block.name, f"{body}{probes}{footer}", lean)
            sizes = [int(n) for n in re.findall(r"^(\d+)\s*$", probe.stdout, re.M)]
            if probe.returncode != 0 or len(sizes) != (2 if with_folds else 1):
                error = _first_line(probe)
                continue
            text = body + f"theorem use : Nat.add {OFFSET} (sizeOf {value}) = {OFFSET + sizes[0]} := rfl\n"
            names = [f"{block.name}.use"]
            if with_folds:
                text += f"\ntheorem fold : Nat.add {FOLD_OFFSET} ({fold} {value}) = {FOLD_OFFSET + sizes[1]} := rfl\n"
                names.append(f"{block.name}.fold")
            text += footer
            compiled = _compile(directory, block.name, text, lean)
            if compiled.returncode != 0:
                error = _first_line(compiled)
                continue
            exported = subprocess.run(
                [leanexport, block.name, "--", *names],
                capture_output=True, text=True, cwd=directory, timeout=300,
                env={**os.environ, "LEAN_PATH": f"{directory}:{prefix}/lib/lean"},
            )
            if exported.returncode != 0:
                return Generated(block.name, text, None, f"leanexport: {exported.stderr.strip()[:200]}")
            results = (FOLD_OFFSET + sizes[1],) if with_folds else ()
            return Generated(block.name, text, exported.stdout, fold=sizes[0], results=results)
    return Generated(block.name, header, None, error)


def generate(
    count: int, seed: int, lean: str = "lean", leanexport: str = "leanexport", workers: int | None = None
) -> list[Generated]:
    rng = random.Random(seed)
    jobs: list[tuple[Block, tuple[str, str]]] = []
    attempts = 0
    while len(jobs) < count and attempts < count * 20:
        attempts += 1
        block = Block(rng, f"PestycydNest{seed}x{attempts}")
        values = block.values()
        if values:
            jobs.append((block, pick_major(values)))
    prefix = _lean_prefix(lean)
    with ThreadPoolExecutor(max_workers=workers or os.cpu_count() or 4) as pool:
        return list(pool.map(lambda job: elaborate(*job, lean, leanexport, prefix), jobs))
