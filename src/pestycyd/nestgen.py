"""Random mutual blocks of deeply nested inductives, measured with ``sizeOf``.

``indgen`` writes the recursor application by hand, which limits it to one
type nested through ``List``.  Here the blocks hold one to three mutual
types, optionally indexed by ``Bool``, whose fields nest the block through
``List``, ``Option``, ``×``, ``Array`` and four containers declared in the
module: ``Rose`` (itself nested), ``Pair2`` (a structure over ``List``),
``Vec`` (indexed) and ``Wrap`` (reflexive), up to three containers deep.
Lean derives ``SizeOf`` for the block through its recursors, one motive per
nested auxiliary type, so

    Nat.add OFFSET (sizeOf v) = OFFSET + N := rfl

drives a checker through every auxiliary recursor at once.  ``N`` comes
from ``#reduce`` (the elaborator's whnf, not the kernel); the theorem is then
compiled, so Lean's kernel confirms it before the module is exported.
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

PRELUDE = {
    "Rose": "inductive Rose (α : Type u) where\n  | node : α → List (Rose α) → Rose α",
    "Pair2": "structure Pair2 (α : Type u) (β : Type u) where\n  fst : α\n  snd : List β",
    "Vec": "inductive Vec (α : Type u) : Nat → Type u where\n  | nil : Vec α 0\n  | cons : α → Vec α n → Vec α (n + 1)",
    "Wrap": "inductive Wrap (α : Type u) : Type u where\n  | none\n  | one : α → Wrap α\n  | many : (Bool → Wrap α) → Wrap α",
}
CONTAINERS = ("List", "Option", "Prod", "Array", "Rose", "Pair2", "Vec", "Wrap")
# A field type is a tuple: ("bool",), ("nat",), ("ref", T, index|None),
# ("refl", ref) for Bool → ref, or (container, inner[, second]).
FieldType = tuple


class Block:
    def __init__(self, rng: random.Random, name: str) -> None:
        self.rng, self.name = rng, name
        self.types = [f"T{i}" for i in range(rng.choice((1, 2, 2, 3)))]
        self.indexed = {t: rng.random() < 0.4 for t in self.types}
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
        self.used.add(container)
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

    def show(self, ty: FieldType) -> str:
        kind = ty[0]
        if kind == "bool":
            return "Bool"
        if kind == "nat":
            return "Nat"
        if kind == "ref":
            return f"{ty[1]} {ty[2]}" if ty[2] else ty[1]
        if kind == "refl":
            return f"Bool → {self.show(ty[1])}"
        if kind == "Prod":
            return f"({self.show(ty[1])} × {self.show(ty[2])})"
        if kind == "Pair2":
            return f"(Pair2 ({self.show(ty[1])}) ({self.show(ty[2])}))"
        if kind == "Vec":
            return f"(Vec ({self.show(ty[1])}) 2)"
        return f"({kind} ({self.show(ty[1])}))"

    def declaration(self) -> str:
        lines = []
        for t in self.types:
            lines.append(f"inductive {t} : {'Bool → Type' if self.indexed[t] else 'Type'} where")
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
        if kind == "Rose":
            kids = [f"(Rose.node {x} [])" for x in some(ty[1], (0, 1, 2))]
            return f"(Rose.node {first} [{', '.join(kids)}])"
        r = rng.random()  # Wrap
        if r < 0.2:
            return "Wrap.none"
        return f"(Wrap.one {first})" if r < 0.6 else f"(Wrap.many (fun b => if b then Wrap.one {first} else Wrap.none))"

    def values(self, rounds: int = 30) -> list[str]:
        """Closed terms bottom-up, grouped by type and index."""
        pool: dict[tuple[str, str | None], list[str]] = {}
        for _ in range(rounds):
            t = self.rng.choice(self.types)
            number = self.rng.randrange(len(self.ctors[t]))
            fields, index = self.ctors[t][number]
            args = [self.term(item, pool) for item in fields]
            if all(arg is not None for arg in args):
                pool.setdefault((t, index), []).append(" ".join([f"{t}.c{number}", *args]))  # type: ignore[list-item]
        return [value for values in pool.values() for value in values]

    def header(self) -> str:
        containers = "\n\n".join(text for name, text in PRELUDE.items() if name in self.used)
        return f"universe u\n\n{containers}\n\nnamespace {self.name}\n\n{self.declaration()}\n\n"


def pick_major(values: list[str]) -> str:
    major = max(values, key=len)
    return major if len(major) <= 1500 else min(values, key=lambda value: abs(len(value) - 600))


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


def elaborate(block: Block, major: str, lean: str, leanexport: str, prefix: str) -> Generated:
    header, footer = block.header(), f"\nend {block.name}\n"
    with tempfile.TemporaryDirectory(prefix="pestycyd-nestgen-") as directory:
        probe = _compile(directory, block.name, f"{header}#reduce sizeOf ({major})\n{footer}", lean)
        size = re.search(r"^(\d+)\s*$", probe.stdout, re.M)
        if probe.returncode != 0 or size is None:
            return Generated(block.name, header, None, _first_line(probe))
        fold = int(size.group(1))
        text = f"{header}theorem use : Nat.add {OFFSET} (sizeOf ({major})) = {OFFSET + fold} := rfl\n{footer}"
        compiled = _compile(directory, block.name, text, lean)
        if compiled.returncode != 0:
            return Generated(block.name, text, None, _first_line(compiled))
        exported = subprocess.run(
            [leanexport, block.name, "--", f"{block.name}.use"],
            capture_output=True, text=True, cwd=directory, timeout=300,
            env={**os.environ, "LEAN_PATH": f"{directory}:{prefix}/lib/lean"},
        )
        if exported.returncode != 0:
            return Generated(block.name, text, None, f"leanexport: {exported.stderr.strip()[:200]}")
        return Generated(block.name, text, exported.stdout, fold=fold)


def generate(
    count: int, seed: int, lean: str = "lean", leanexport: str = "leanexport", workers: int | None = None
) -> list[Generated]:
    rng = random.Random(seed)
    jobs: list[tuple[Block, str]] = []
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
