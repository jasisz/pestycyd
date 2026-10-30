"""Graph-level rewriting of lean4export NDJSON documents.

The export format keeps three intern tables (names, levels, expressions)
whose identifiers are dense, sequential, and referenced strictly backward.
Any transformation that inserts or removes a record therefore has to
renumber a whole table and rewrite every reference to it.  This module
owns that machinery plus two consumers of it:

- ``canonicalize`` drops records unreachable from the declarations and
  renumbers the remainder, giving an equivalent minimal presentation;
- the metamorphic transforms in :mod:`pestycyd.transforms` insert fresh
  records through the same renumbering core.

Everything here is deterministic: no randomness, no wall-clock input.
"""

from __future__ import annotations

import copy
import json
from typing import Iterator

from .ndjson import Document

DECLARATION_KINDS = ("axiom", "def", "thm", "opaque")
INDUCTIVE_GROUPS = ("types", "ctors", "recs")

# Records inserted by transforms carry this marker instead of a table id;
# the renumbering core assigns the next identifier and removes the marker.
FRESH = "__pestycyd_fresh__"


def declares_table_id(line: dict[str, object]) -> tuple[str, int] | None:
    for key in ("in", "il", "ie"):
        value = line.get(key)
        if isinstance(value, int) and not isinstance(value, bool):
            return key, value
    return None


def is_declaration(line: dict[str, object]) -> bool:
    return any(key in line for key in (*DECLARATION_KINDS, "inductive", "quot"))


def expression_reference_sites(line: dict[str, object]) -> Iterator[tuple[tuple[object, ...], str]]:
    """Yield ``(path, field)`` for every expression-table reference in a line."""
    app = line.get("app")
    if isinstance(app, dict):
        for field in ("fn", "arg"):
            yield ("app",), field
    for binder in ("lam", "forallE"):
        obj = line.get(binder)
        if isinstance(obj, dict):
            yield (binder,), "type"
            yield (binder,), "body"
    let_expr = line.get("letE")
    if isinstance(let_expr, dict):
        for field in ("type", "value", "body"):
            yield ("letE",), field
    proj = line.get("proj")
    if isinstance(proj, dict):
        yield ("proj",), "struct"
    mdata = line.get("mdata")
    if isinstance(mdata, dict):
        yield ("mdata",), "expr"
    for kind in (*DECLARATION_KINDS, "quot"):
        declaration = line.get(kind)
        if isinstance(declaration, dict):
            for field in ("type", "value"):
                if kind != "quot" or field in declaration:
                    yield (kind,), field
    block = line.get("inductive")
    if isinstance(block, dict):
        for group in INDUCTIVE_GROUPS:
            items = block.get(group)
            if not isinstance(items, list):
                continue
            for index, item in enumerate(items):
                if not isinstance(item, dict):
                    continue
                yield ("inductive", group, index), "type"
                rules = item.get("rules")
                if isinstance(rules, list):
                    for rule_index, rule in enumerate(rules):
                        if isinstance(rule, dict):
                            yield ("inductive", group, index, "rules", rule_index), "rhs"


def name_reference_sites(line: dict[str, object]) -> Iterator[tuple[tuple[object, ...], str]]:
    """Yield ``(path, field)`` for every name-table reference in a line."""
    const = line.get("const")
    if isinstance(const, dict):
        yield ("const",), "name"
    proj = line.get("proj")
    if isinstance(proj, dict):
        yield ("proj",), "typeName"
    for binder in ("lam", "forallE", "letE"):
        obj = line.get(binder)
        if isinstance(obj, dict):
            yield (binder,), "name"
    for kind in (*DECLARATION_KINDS, "quot"):
        declaration = line.get(kind)
        if isinstance(declaration, dict):
            for field in ("name", "levelParams", "all"):
                if field in declaration:
                    yield (kind,), field
    if "in" in line:
        payload = line.get("str") or line.get("num")
        if isinstance(payload, dict):
            yield (), "str" if "str" in line else "num"
    if "il" in line and "param" in line:
        yield (), "param"
    block = line.get("inductive")
    if isinstance(block, dict):
        for group in INDUCTIVE_GROUPS:
            items = block.get(group)
            if not isinstance(items, list):
                continue
            for index, item in enumerate(items):
                if not isinstance(item, dict):
                    continue
                path = ("inductive", group, index)
                for field in ("name", "levelParams", "all", "induct", "ctors"):
                    if field in item:
                        yield path, field
                rules = item.get("rules")
                if isinstance(rules, list):
                    for rule_index, rule in enumerate(rules):
                        if isinstance(rule, dict) and "ctor" in rule:
                            yield (*path, "rules", rule_index), "ctor"


def level_reference_sites(line: dict[str, object]) -> Iterator[tuple[tuple[object, ...], str]]:
    """Yield ``(path, field)`` for every level-table reference in a line."""
    if "sort" in line:
        yield (), "sort"
    const = line.get("const")
    if isinstance(const, dict):
        yield ("const",), "us"
    if "il" in line:
        for field in ("succ", "max", "imax"):
            if field in line:
                yield (), field


def _resolve(line: dict[str, object], path: tuple[object, ...]) -> dict[str, object] | None:
    current: object = line
    for part in path:
        if isinstance(current, dict):
            if part not in current:
                return None
            current = current[part]
        elif isinstance(current, list):
            if not isinstance(part, int) or not 0 <= part < len(current):
                return None
            current = current[part]
        else:
            return None
    return current if isinstance(current, dict) else None


def _map_int(value: object, mapping: dict[int, int]) -> object:
    if isinstance(value, int) and not isinstance(value, bool):
        return mapping.get(value, value)
    return value


def _dangling(value: object, mapping: dict[int, int], implicit_zero: bool) -> bool:
    """A table reference that resolves to no record.

    Names and levels have an implicit identifier 0 (the root name and the
    zero universe); the expression table does not — its identifier 0 is an
    ordinary record.  Negative values are local placeholders used by the
    transform fragments and are resolved separately.
    """
    return (
        isinstance(value, int)
        and not isinstance(value, bool)
        and value >= 0
        and value not in mapping
        and not (implicit_zero and value == 0)
    )


def _rewrite_references(
    line: dict[str, object],
    expressions: dict[int, int],
    names: dict[int, int],
    levels: dict[int, int],
    strict: bool = True,
) -> None:
    """Rewrite table references through ``expressions``/``names``/``levels``.

    With ``strict`` (the default) a reference missing from the mapping is
    an error, which protects renumbering from accidentally capturing a
    dangling identifier onto an unrelated record.  Transform fragments use
    ``strict=False`` to substitute their negative local placeholders with
    a partial mapping after renumbering has already validated everything.
    """

    def check(value: object, mapping: dict[int, int], implicit_zero: bool, kind: str) -> None:
        if strict and _dangling(value, mapping, implicit_zero):
            raise ValueError(f"dangling {kind} reference")

    for path, field in expression_reference_sites(line):
        owner = _resolve(line, path)
        if owner is not None and field in owner:
            check(owner[field], expressions, implicit_zero=False, kind="expression")
            owner[field] = _map_int(owner[field], expressions)
    for path, field in name_reference_sites(line):
        owner = _resolve(line, path)
        if owner is None or field not in owner:
            continue
        value = owner[field]
        if isinstance(value, list):
            for item in value:
                check(item, names, implicit_zero=True, kind="name")
            owner[field] = [_map_int(item, names) for item in value]
        elif field in {"str", "num"} and isinstance(value, dict):
            check(value.get("pre"), names, implicit_zero=True, kind="name")
            value["pre"] = _map_int(value.get("pre"), names)
        else:
            check(value, names, implicit_zero=True, kind="name")
            owner[field] = _map_int(value, names)
    for path, field in level_reference_sites(line):
        owner = _resolve(line, path)
        if owner is None or field not in owner:
            continue
        value = owner[field]
        if isinstance(value, list):
            for item in value:
                check(item, levels, implicit_zero=True, kind="level")
            owner[field] = [_map_int(item, levels) for item in value]
        else:
            check(value, levels, implicit_zero=True, kind="level")
            owner[field] = _map_int(value, levels)


def _renumber(
    lines: list[dict[str, object]], keep: list[bool] | None = None
) -> list[dict[str, object]] | None:
    """Assign dense sequential table identifiers and rewrite every reference.

    Returns ``None`` when the input relies on duplicate table identifiers:
    renumbering would silently erase the very defect such documents carry
    (for example intern-table shadowing findings).
    """
    seen: set[tuple[str, int]] = set()
    kept = lines if keep is None else [line for line, flag in zip(lines, keep) if flag]
    for line in kept:
        declared = declares_table_id(line)
        if declared is None:
            continue
        if declared in seen:
            return None
        seen.add(declared)

    name_map: dict[int, int] = {0: 0}
    level_map: dict[int, int] = {0: 0}
    expression_map: dict[int, int] = {}
    next_name, next_level, next_expression = 1, 1, 0
    rewritten: list[dict[str, object]] = []
    for line in kept:
        line = copy.deepcopy(line)
        fresh = line.pop(FRESH, None)
        if fresh in {"in", "il", "ie"}:
            line[fresh] = {"in": next_name, "il": next_level, "ie": next_expression}[fresh]
        else:
            declared = declares_table_id(line)
            if declared is not None:
                table, identifier = declared
                if table == "in":
                    name_map[identifier] = next_name
                    line["in"] = next_name
                elif table == "il":
                    level_map[identifier] = next_level
                    line["il"] = next_level
                else:
                    expression_map[identifier] = next_expression
                    line["ie"] = next_expression
        if "in" in line:
            next_name += 1
        elif "il" in line:
            next_level += 1
        elif "ie" in line:
            next_expression += 1
        rewritten.append(line)
    for line in rewritten:
        _rewrite_references(line, expression_map, name_map, level_map)
    return rewritten


def _tables(lines: list[dict[str, object]]) -> tuple[dict[int, int], dict[int, int], dict[int, int]]:
    names: dict[int, int] = {}
    levels: dict[int, int] = {}
    expressions: dict[int, int] = {}
    for index, line in enumerate(lines):
        declared = declares_table_id(line)
        if declared is None:
            continue
        table, identifier = declared
        if table == "in":
            names[identifier] = index
        elif table == "il":
            levels[identifier] = index
        else:
            expressions[identifier] = index
    return names, levels, expressions


def _reachable_lines(lines: list[dict[str, object]]) -> list[bool]:
    """Mark lines reachable from meta and declaration records."""
    names, levels, expressions = _tables(lines)
    keep = ["meta" in line or is_declaration(line) for line in lines]
    changed = True
    while changed:
        changed = False
        for index, line in enumerate(lines):
            if not keep[index]:
                continue
            for path, field in expression_reference_sites(line):
                owner = _resolve(line, path)
                if owner is not None:
                    value = owner.get(field)
                    if isinstance(value, int) and not isinstance(value, bool):
                        target = expressions.get(value)
                        if target is not None and not keep[target]:
                            keep[target] = True
                            changed = True
            for path, field in name_reference_sites(line):
                owner = _resolve(line, path)
                if owner is None:
                    continue
                value = owner.get(field)
                if isinstance(value, dict):
                    # An interned-name record: its "pre" is a name reference.
                    value = value.get("pre")
                values = value if isinstance(value, list) else [value]
                for item in values:
                    if not isinstance(item, int) or isinstance(item, bool):
                        continue
                    if item == 0:
                        continue
                    target = names.get(item)
                    if target is not None and not keep[target]:
                        keep[target] = True
                        changed = True
            for path, field in level_reference_sites(line):
                owner = _resolve(line, path)
                if owner is None:
                    continue
                value = owner.get(field)
                values = value if isinstance(value, list) else [value]
                for item in values:
                    if not isinstance(item, int) or isinstance(item, bool):
                        continue
                    if item == 0:
                        continue
                    target = levels.get(item)
                    if target is not None and not keep[target]:
                        keep[target] = True
                        changed = True
    return keep


def canonicalize(document: Document) -> Document | None:
    """Drop unreachable records and renumber tables densely.

    The result is an equivalent document in a canonical presentation:
    two inputs that differ only in unreachable records or in identifier
    allocation render to identical bytes.  Returns ``None`` when the
    document contains duplicate table identifiers, where renumbering
    would destroy the defect under study.
    """
    lines = list(document.lines)
    # The duplicate check must run before garbage collection: a duplicate
    # intern entry looks unreachable to the closure walk (the table map
    # keeps only one line per identifier) but deleting it would silently
    # resolve the very ambiguity the document is testing.
    seen: set[tuple[str, int]] = set()
    for line in lines:
        declared = declares_table_id(line)
        if declared is None:
            continue
        if declared in seen:
            return None
        seen.add(declared)
    keep = _reachable_lines(lines)
    if not any(keep):
        return None
    try:
        rewritten = _renumber(lines, keep)
    except ValueError:
        return None
    if rewritten is None:
        return None
    return Document(tuple(rewritten))


# Constants the official kernel special-cases by name (literal fast paths,
# string-literal expansion, quotient reduction).  Lean's threat model trusts
# the official prelude for these: replacing one is adversarial input, not a
# kernel bug (lean4#15908, "Kernel bug hunt" guide), so a hunt must never
# mutate them or anything they depend on.
TRUSTED_PRELUDE = frozenset(
    {
        "Nat", "Nat.add", "Nat.sub", "Nat.mul", "Nat.div", "Nat.mod", "Nat.gcd",
        "Nat.beq", "Nat.ble", "Nat.land", "Nat.lor", "Nat.xor", "Nat.shiftLeft",
        "Nat.shiftRight", "Nat.pow", "Nat.log2", "Nat.pred",
        "String", "String.mk", "String.ofList", "Char", "Char.ofNat", "List", "Bool",
        "Eq", "Quot", "Quot.mk", "Quot.lift", "Quot.ind",
        # Binder annotations the kernel strips by name when it generates
        # recursors; kefir declines a block whose outParam is not the identity.
        "outParam", "optParam", "autoParam",
    }
)


def _name_strings(lines: list[dict[str, object]]) -> dict[int, str]:
    names: dict[int, str] = {0: ""}
    for line in lines:
        identifier = line.get("in")
        if not isinstance(identifier, int):
            continue
        payload = line.get("str") or line.get("num")
        if not isinstance(payload, dict):
            continue
        prefix = names.get(payload.get("pre"), "")  # type: ignore[arg-type]
        part = payload.get("str") if "str" in line else payload.get("i")
        names[identifier] = f"{prefix}.{part}" if prefix else str(part)
    return names


def _declared(line: dict[str, object]) -> list[int]:
    for kind in (*DECLARATION_KINDS, "quot"):
        declaration = line.get(kind)
        if isinstance(declaration, dict) and isinstance(declaration.get("name"), int):
            return [declaration["name"]]
    block = line.get("inductive")
    if not isinstance(block, dict):
        return []
    return [
        item["name"]
        for group in INDUCTIVE_GROUPS
        for item in block.get(group, [])
        if isinstance(item, dict) and isinstance(item.get("name"), int)
    ]


def prelude_lines(document: Document, trusted: frozenset[str] = TRUSTED_PRELUDE) -> frozenset[int]:
    """Return the lines defining trusted prelude constants and everything they reach.

    The closure follows expression, level, and name references and, through
    ``const`` nodes, the declarations of referenced constants: rewriting
    ``Nat.brecOn`` changes ``Nat.add`` as surely as rewriting ``Nat.add``.
    """
    lines = list(document.lines)
    names = _name_strings(lines)
    tables: dict[tuple[str, int], int] = {}
    declarations: dict[int, int] = {}
    for line_no, line in enumerate(lines):
        declared = declares_table_id(line)
        if declared is not None:
            tables[declared] = line_no
        for name in _declared(line):
            declarations.setdefault(name, line_no)

    pending = [line_no for name, line_no in declarations.items() if names.get(name) in trusted]
    protected: set[int] = set()
    while pending:
        line_no = pending.pop()
        if line_no in protected:
            continue
        protected.add(line_no)
        line = lines[line_no]
        references: list[tuple[str, object]] = []
        for key, sites in (
            ("ie", expression_reference_sites),
            ("in", name_reference_sites),
            ("il", level_reference_sites),
        ):
            for path, field in sites(line):
                obj = _resolve(line, path)
                if obj is not None and field in obj:
                    references.append((key, obj[field]))
        quot = line.get("quot")
        if isinstance(quot, dict):
            references += [("in", quot.get("name")), ("in", quot.get("levelParams")), ("ie", quot.get("type"))]
        const = line.get("const")
        if isinstance(const, dict) and const.get("name") in declarations:
            pending.append(declarations[const["name"]])  # type: ignore[index]
        for key, value in references:
            if key == "in" and isinstance(value, dict):
                value = value.get("pre")
            for identifier in value if isinstance(value, list) else [value]:
                if isinstance(identifier, int) and (key, identifier) in tables:
                    pending.append(tables[(key, identifier)])
    return frozenset(protected)


def share(document: Document) -> Document | None:
    """Merge structurally equal table records, then renumber densely.

    Lean's exporter interns every name, level and expression once; hand-
    assembled documents can repeat one (``bvar 0`` from two fragments).  The
    official kernel tolerates that, but nanoda-family checkers refuse it
    (``Attempted to insert duplicate Name``/``Expr``), which hides every
    other verdict of theirs on the document.  Records reference only earlier
    ones, so one pass in order sees each record with its references already
    merged.
    """
    seen: set[tuple[str, int]] = set()
    for line in document.lines:
        declared = declares_table_id(line)
        if declared is not None:
            if declared in seen:
                return None
            seen.add(declared)
    merged: dict[str, dict[int, int]] = {"in": {}, "il": {}, "ie": {}}
    canonical: dict[tuple[str, str], int] = {}
    kept: list[dict[str, object]] = []
    for line in document.lines:
        line = copy.deepcopy(line)
        _rewrite_references(line, merged["ie"], merged["in"], merged["il"], strict=False)
        declared = declares_table_id(line)
        if declared is not None:
            table, identifier = declared
            key = (table, json.dumps({k: v for k, v in line.items() if k != table}, sort_keys=True))
            if key in canonical:
                merged[table][identifier] = canonical[key]
                continue
            canonical[key] = identifier
        kept.append(line)
    try:
        rewritten = _renumber(kept)
    except ValueError:
        return None
    return None if rewritten is None else Document(tuple(rewritten))


def _share_key(table: str, line: dict[str, object]) -> tuple[str, str]:
    return table, json.dumps({k: v for k, v in line.items() if k != table}, sort_keys=True)


# Share indexes of recent bases, keyed by identity; the base is kept alive
# beside its index so the identity cannot be reused while cached.
_SHARE_INDEXES: dict[int, tuple[Document, tuple[dict[tuple[str, str], int], dict[str, int]] | None]] = {}


def _share_index(base: Document) -> tuple[dict[tuple[str, str], int], dict[str, int]] | None:
    """Structure keys and next free ids of an already-shared base, or ``None``."""
    cached = _SHARE_INDEXES.get(id(base))
    if cached is not None and cached[0] is base:
        return cached[1]
    canonical: dict[tuple[str, str], int] = {}
    seen: set[tuple[str, int]] = set()
    next_ids = {"in": 1, "il": 1, "ie": 0}
    index: tuple[dict[tuple[str, str], int], dict[str, int]] | None = (canonical, next_ids)
    for line in base.lines:
        if FRESH in line:
            index = None
            break
        declared = declares_table_id(line)
        if declared is None:
            continue
        table, identifier = declared
        key = _share_key(table, line)
        if declared in seen or key in canonical:
            index = None
            break
        seen.add(declared)
        canonical[key] = identifier
        next_ids[table] = max(next_ids[table], identifier + 1)
    if len(_SHARE_INDEXES) >= 8:
        _SHARE_INDEXES.clear()
    _SHARE_INDEXES[id(base)] = (base, index)
    return index


def share_appended(base: Document, document: Document) -> Document | None:
    """``share`` for a document that extends ``base`` by appended records.

    When ``base`` is itself shared, only the appended tail can repeat a
    record, so the tail is merged against a cached index of the base and
    renumbered past it; the base lines are reused untouched.  That keeps
    appending campaigns from re-hashing a large seed on every mutation.
    Falls back to ``share`` whenever that premise does not hold.
    """
    start = len(base.lines)
    index = _share_index(base)
    if index is None or len(document.lines) < start or document.lines[:start] != base.lines:
        return share(document)
    canonical, next_ids = dict(index[0]), dict(index[1])
    merged: dict[str, dict[int, int]] = {"in": {}, "il": {}, "ie": {}}
    tail: list[dict[str, object]] = []
    for line in document.lines[start:]:
        if FRESH in line:
            return share(document)
        line = copy.deepcopy(line)
        _rewrite_references(line, merged["ie"], merged["in"], merged["il"], strict=False)
        declared = declares_table_id(line)
        if declared is not None:
            table, identifier = declared
            if identifier < index[1][table]:
                return share(document)
            key = _share_key(table, line)
            if key in canonical:
                merged[table][identifier] = canonical[key]
                continue
            merged[table][identifier] = canonical[key] = line[table] = next_ids[table]  # type: ignore[assignment]
            next_ids[table] += 1
        tail.append(line)
    return Document((*base.lines, *tail))


def renumber(document: Document) -> Document | None:
    """Renumber tables densely without dropping any records."""
    try:
        rewritten = _renumber(list(document.lines))
    except ValueError:
        return None
    if rewritten is None:
        return None
    return Document(tuple(rewritten))


# --- canonical false-theorem detection -------------------------------------


def _level_is_zero(identifier: int, levels: dict[int, dict[str, object]]) -> bool:
    if identifier == 0:
        return True
    line = levels.get(identifier)
    if line is None:
        return False
    if "succ" in line or "param" in line:
        return False
    for key in ("max", "imax"):
        operands = line.get(key)
        if isinstance(operands, list) and len(operands) == 2:
            return all(
                isinstance(value, int)
                and _level_is_zero(value, levels)
                for value in operands
            )
    return False


def _document_is_axiom_free(lines: list[dict[str, object]]) -> bool:
    for line in lines:
        if "axiom" in line:
            return False
        definition = line.get("def")
        if isinstance(definition, dict) and definition.get("safety") != "safe":
            return False
        opaque = line.get("opaque")
        if isinstance(opaque, dict) and opaque.get("isUnsafe") is True:
            return False
        block = line.get("inductive")
        if not isinstance(block, dict):
            continue
        for group in INDUCTIVE_GROUPS:
            items = block.get(group)
            if not isinstance(items, list):
                continue
            for item in items:
                if isinstance(item, dict) and item.get("isUnsafe") is True:
                    return False
    return True


def canonical_false_theorem(document: Document) -> bool:
    """Detect the escalation target ``∀ P : Prop, P`` as the final theorem.

    This is a structural check, deliberately independent of interned names:
    a shadowed ``False`` constant cannot sneak past it, and neither can a
    theorem that quietly assumes an axiom or lives in the unsafe fragment.
    A goal wrapped in level-free definitions (``def T := ∀ P : Prop, P``
    proved as ``thm : T``) is unwrapped before the check, mirroring the
    delta reduction any kernel would perform.
    """
    lines = list(document.lines)
    if not _document_is_axiom_free(lines):
        return False
    expressions = {
        identifier: line
        for line in lines
        if (declared := declares_table_id(line)) is not None and declared[0] == "ie"
        for identifier in (declared[1],)
    }
    levels = {
        identifier: line
        for line in lines
        if (declared := declares_table_id(line)) is not None and declared[0] == "il"
        for identifier in (declared[1],)
    }
    definitions: dict[int, int] = {}
    for line in lines:
        for kind in ("def", "thm", "opaque"):
            payload = line.get(kind)
            if (
                isinstance(payload, dict)
                and isinstance(payload.get("name"), int)
                and not payload.get("levelParams")
                and isinstance(payload.get("value"), int)
            ):
                definitions[payload["name"]] = payload["value"]
    final: dict[str, object] | None = None
    for line in lines:
        if is_declaration(line):
            theorem = line.get("thm")
            final = theorem if isinstance(theorem, dict) else {}
    if not final or not isinstance(final.get("value"), int):
        return False
    root = final.get("type")
    if not isinstance(root, int) or isinstance(root, bool):
        return False
    unfolded = 0
    seen: set[int] = set()
    while unfolded < 8:
        if root in seen:
            return False
        seen.add(root)
        line = expressions.get(root)
        if line is None:
            return False
        const = line.get("const")
        if not isinstance(const, dict):
            break
        name, universes = const.get("name"), const.get("us")
        if (
            not isinstance(name, int)
            or isinstance(name, bool)
            or universes
            or name not in definitions
        ):
            # Not a definition reference: maybe an inductive constant,
            # which the tail handles separately.
            break
        root = definitions[name]
        unfolded += 1
    forall = expressions.get(root)
    if forall is None:
        return False
    if "const" in forall:
        # The second canonical shape: a closed proof of an inductive type
        # with zero constructors living in Prop.  Proving any such type is
        # exactly as strong as proving False.
        const = forall["const"]
        name, universes = const.get("name"), const.get("us")
        if not isinstance(name, int) or isinstance(name, bool) or universes:
            return False
        for line in lines:
            block = line.get("inductive")
            if not isinstance(block, dict):
                continue
            for item in block.get("types", []):
                if not isinstance(item, dict) or item.get("name") != name:
                    continue
                if item.get("ctors"):
                    return False
                item_type = expressions.get(item.get("type"))
                if item_type is None or "sort" not in item_type:
                    return False
                return _level_is_zero(item_type["sort"], levels)  # type: ignore[arg-type]
        return False
    if "forallE" not in forall:
        return False
    binder = forall["forallE"]
    if not isinstance(binder, dict):
        return False
    domain, body = binder.get("type"), binder.get("body")
    if not isinstance(domain, int) or not isinstance(body, int):
        return False
    domain_line = expressions.get(domain)
    if domain_line is None or "sort" not in domain_line:
        return False
    if not _level_is_zero(domain_line["sort"], levels):  # type: ignore[arg-type]
        return False
    body_line = expressions.get(body)
    return body_line is not None and body_line.get("bvar") == 0
