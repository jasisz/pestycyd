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

import os
import random
import subprocess
import tempfile
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

from .indgen import Generated, _lean_prefix

SORTS = (
    "Prop", "Prop", "Prop", "Sort u", "Sort u", "Sort (imax u v)", "Sort (max u v)", "Sort (imax v u)",
    "Sort (max 1 u)", "Sort (imax 1 u)", "Sort (imax u 0)", "Sort (max u 0)", "Sort (u + 1)",
    "Sort (imax (u + 1) v)", "Sort (max 0 u)",
)
PARAMS = (("α", "Sort u"), ("β", "Sort v"), ("p", "Prop"), ("γ", "Type"), ("n", "Nat"))
INDICES = ("Nat", "Bool", "Prop", "α", "Sort u")


class Family:
    def __init__(self, rng: random.Random, name: str) -> None:
        self.rng, self.name = rng, name
        self.mutual = rng.random() < 0.3
        self.sort = rng.choice(SORTS)
        self.params = rng.sample(PARAMS, rng.choice((0, 1, 1, 2, 3)))
        self.names = {param for param, _ in self.params}
        pool = [index for index in INDICES if index != "α" or "α" in self.names]
        self.types = [f"T{i}" for i in range(rng.choice((2, 2, 3)) if self.mutual else 1)]
        self.indices = {t: [rng.choice(pool) for _ in range(rng.choice((0, 0, 1, 1, 2)))] for t in self.types}

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
        kind = self.rng.choice(("proof", "data", "data", "rec", "eq"))
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

    def source(self) -> str:
        binders = "".join(f" ({param} : {ty})" for param, ty in self.params)
        lines = []
        for t in self.types:
            lines.append(f"inductive {t}{'' if self.mutual else binders} : {' → '.join([*self.indices[t], self.sort])} where")
            for number in range(self.rng.choice((0, 1, 1, 1, 2))):
                fields: list[tuple[str, str]] = []
                for j in range(self.rng.choice((0, 1, 2, 3))):
                    ty = self.field_type(fields)
                    if ty is not None:
                        fields.append((f"x{j}", ty))
                values = [self.value(index, fields) for index in self.indices[t]]
                if None in values:
                    continue
                parts = [f"({field} : {ty})" for field, ty in fields]
                lines.append(f"  | c{number} : {' → '.join([*parts, self.applied(t, values)])}")  # type: ignore[list-item]
        body = "\n".join(lines)
        if self.mutual:
            variables = f"variable{binders}\n" if self.params else ""
            body = f"section\n{variables}mutual\n{body}\nend\nend"
        return (
            "universe u v\n\nset_option bootstrap.inductiveCheckResultingUniverse false\n\n"
            f"namespace {self.name}\n\n{body}\n\nend {self.name}\n"
        )


def elaborate(family: Family, lean: str, leanexport: str, prefix: str) -> Generated:
    text = family.source()
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
        exported = subprocess.run(
            [leanexport, family.name, "--", f"{family.name}.{family.types[0]}"],
            capture_output=True, text=True, cwd=directory, timeout=120,
            env={**os.environ, "LEAN_PATH": f"{directory}:{prefix}/lib/lean"},
        )
        if exported.returncode != 0:
            return Generated(family.name, text, None, f"leanexport: {exported.stderr.strip()[:200]}")
        return Generated(family.name, text, exported.stdout)


def generate(
    count: int, seed: int, lean: str = "lean", leanexport: str = "leanexport", workers: int | None = None
) -> list[Generated]:
    rng = random.Random(seed)
    families = [Family(rng, f"PestycydProp{seed}x{number}") for number in range(count)]
    prefix = _lean_prefix(lean)
    with ThreadPoolExecutor(max_workers=workers or os.cpu_count() or 4) as pool:
        return list(pool.map(lambda family: elaborate(family, lean, leanexport, prefix), families))
