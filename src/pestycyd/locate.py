"""Per-declaration verdicts from whole-file checkers.

Every kernel in the matrix answers once per document, so a disagreement
says *that* checkers split but not *where*.  Lean exports are processed
in order and a checker stops at the first declaration it refuses, which
makes a kernel's verdict monotone in the document prefix: it accepts
every prefix up to the offending declaration and refuses every prefix
that contains it.  ``locate`` binary-searches that boundary per kernel.

A prefix ends with its last declaration.  Intern-table records are
referenced strictly backward, so a truncated export stays well-formed
without renumbering — which also preserves inputs whose defect is a
re-bound table identifier.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Callable

from .ndjson import Document
from .rewrite import _declared, _name_strings, declares_table_id, is_declaration


@dataclass(frozen=True)
class Declaration:
    index: int
    line: int
    kind: str
    names: tuple[str, ...]

    @property
    def label(self) -> str:
        shown = ", ".join(self.names[:3])
        if len(self.names) > 3:
            shown += f", +{len(self.names) - 3}"
        return f"#{self.index} {self.kind} {shown}".rstrip()


def declarations(document: Document) -> list[Declaration]:
    lines = list(document.lines)
    names = _name_strings(lines)
    found: list[Declaration] = []
    for position, line in enumerate(lines):
        if not is_declaration(line):
            continue
        kind = next(key for key in line if key in ("axiom", "def", "thm", "opaque", "inductive", "quot"))
        found.append(
            Declaration(
                index=len(found) + 1,
                line=position,
                kind=kind,
                names=tuple(names.get(identifier, f"<name {identifier}>") for identifier in _declared(line)),
            )
        )
    return found


def prefix(document: Document, found: list[Declaration], count: int) -> Document:
    """The document cut right after its ``count``-th declaration.

    Table records between two declarations belong to the later one, so
    they are cut with it; the empty prefix keeps only the header.
    """
    if count >= len(found):
        return document
    if count > 0:
        return Document(tuple(document.lines[: found[count - 1].line + 1]))
    header = []
    for line in document.lines:
        if declares_table_id(line) is not None or is_declaration(line):
            break
        header.append(line)
    return Document(tuple(header))


def first_refusal(count: int, accepts: Callable[[int], bool]) -> int | None:
    """Smallest prefix size ``k`` in ``1..count`` that ``accepts`` refuses.

    ``accepts(count)`` is assumed false (the caller already saw the full
    document refused); ``None`` means even the declaration-free prefix
    is refused, i.e. the header or tables alone are the problem.
    """
    if not accepts(0):
        return None
    low, high = 0, count  # accepts(low) and not accepts(high)
    while high - low > 1:
        middle = (low + high) // 2
        if accepts(middle):
            low = middle
        else:
            high = middle
    return high
