"""Validity-preserving document transforms for metamorphic campaigns.

Every transform here takes a well-formed export of a correct input and
returns a document that must be accepted by any conforming checker:
the oracle ``guaranteed-accept`` in :mod:`pestycyd.campaigns` relies on
that construction.  Applicability conditions are checked by the campaign
generators; the transforms raise ``ValueError`` when handed a document
that violates them.
"""

from __future__ import annotations

import copy

from .ndjson import Document, Rewrite
from .rewrite import (
    FRESH,
    _renumber,
    _resolve,
    _rewrite_references,
    declares_table_id,
    expression_reference_sites,
    is_declaration,
    share,
)


def _fragment_with_local_ids(
    lines: list[dict[str, object]], position: int, fragment: list[dict[str, object]]
) -> tuple[list[dict[str, object]], dict[int, int]]:
    """Insert ``fragment`` at ``position`` and renumber the whole document.

    Fragment records cross-reference each other with negative local
    identifiers (``-1`` is the first record, ``-2`` the second, ...).
    The returned mapping resolves those local identifiers to the real
    expression identifiers the renumbering assigned.
    """
    inserted = [copy.deepcopy(record) for record in fragment]
    combined = lines[:position] + inserted + lines[position:]
    try:
        result = _renumber(combined)
    except ValueError as failure:
        raise ValueError(f"document cannot be renumbered: {failure}") from failure
    if result is None:
        raise ValueError("document contains duplicate table identifiers")
    local = {
        -(index + 1): value
        for index in range(len(inserted))
        if isinstance((value := result[position + index].get("ie")), int)
    }
    if len(local) != len(inserted):
        raise ValueError("fragment records did not receive expression identifiers")
    for index in range(len(inserted)):
        _rewrite_references(result[position + index], local, {}, {}, strict=False)
    return result, local


def _fix_local(
    lines: list[dict[str, object]], positions: list[int], local: dict[int, int]
) -> None:
    for position in positions:
        _rewrite_references(lines[position], local, {}, {}, strict=False)


def _declaration(lines: list[dict[str, object]], line_no: int, path: tuple[object, ...]):
    declaration = _resolve(lines[line_no], path)
    if not isinstance(declaration, dict):
        raise ValueError("rewrite path does not name a declaration")
    return declaration


def wrap_beta(document: Document, line_no: int, path: tuple[object, ...]) -> Document:
    """Replace ``v`` with ``((fun x : T => x) v)`` for a declaration ``T := v``."""
    lines = list(document.lines)
    declaration = _declaration(lines, line_no, path)
    type_id, value_id = declaration.get("type"), declaration.get("value")
    if not isinstance(type_id, int) or not isinstance(value_id, int):
        raise ValueError("declaration needs typed value")
    fragment = [
        {FRESH: "ie", "bvar": 0},
        {
            FRESH: "ie",
            "lam": {
                "binderInfo": "default",
                "name": 0,
                "type": type_id,
                "body": -1,
            },
        },
        {FRESH: "ie", "app": {"fn": -2, "arg": value_id}},
    ]
    declaration["value"] = -3
    result, local = _fragment_with_local_ids(lines, line_no, fragment)
    _fix_local(result, [line_no + len(fragment)], local)
    return Document(tuple(result))


def wrap_eta(document: Document, line_no: int, path: tuple[object, ...]) -> Document:
    """Replace ``v`` with ``fun x => v x`` when the declaration type is a Pi.

    Eta is definitional in Lean's kernel, so the expanded lambda has the
    same type and the same normal form as the original value.  The domain
    of the new binder is taken from the declaration's own serialized Pi
    type, which keeps the transform type-directed without inventing a
    type checker.
    """
    lines = list(document.lines)
    declaration = _declaration(lines, line_no, path)
    type_id, value_id = declaration.get("type"), declaration.get("value")
    if not isinstance(type_id, int) or not isinstance(value_id, int):
        raise ValueError("declaration needs typed value")
    table = _expression_table(lines)
    forall = table.get(type_id)
    if not isinstance(forall, dict) or not isinstance(forall.get("forallE"), dict):
        raise ValueError("declaration type is not a Pi")
    domain = forall["forallE"].get("type")
    if not isinstance(domain, int) or isinstance(domain, bool):
        raise ValueError("Pi domain is not an expression reference")
    fragment = [
        {FRESH: "ie", "bvar": 0},
        {FRESH: "ie", "app": {"fn": value_id, "arg": -1}},
        {
            FRESH: "ie",
            "lam": {
                "binderInfo": "default",
                "name": 0,
                "type": domain,
                "body": -2,
            },
        },
    ]
    declaration["value"] = -3
    result, local = _fragment_with_local_ids(lines, line_no, fragment)
    _fix_local(result, [line_no + len(fragment)], local)
    return Document(tuple(result))


def wrap_let(document: Document, line_no: int, path: tuple[object, ...]) -> Document:
    """Replace ``v`` with ``let x : T := v; x`` for a declaration ``T := v``."""
    lines = list(document.lines)
    declaration = _declaration(lines, line_no, path)
    type_id, value_id = declaration.get("type"), declaration.get("value")
    if not isinstance(type_id, int) or not isinstance(value_id, int):
        raise ValueError("declaration needs typed value")
    fragment = [
        {FRESH: "ie", "bvar": 0},
        {
            FRESH: "ie",
            "letE": {
                "name": 0,
                "nondep": False,
                "type": type_id,
                "value": value_id,
                "body": -1,
            },
        },
    ]
    declaration["value"] = -2
    result, local = _fragment_with_local_ids(lines, line_no, fragment)
    _fix_local(result, [line_no + len(fragment)], local)
    return Document(tuple(result))


def _name_strings(lines: list[dict[str, object]]) -> set[str]:
    strings: set[str] = set()
    for line in lines:
        payload = line.get("str")
        if isinstance(payload, dict) and isinstance(payload.get("str"), str):
            strings.add(payload["str"])
    return strings


def _rename_sites(line: dict[str, object]):
    """Name references whose identity is the renamed declaration, not a binder."""
    const = line.get("const")
    if isinstance(const, dict):
        yield ("const",), "name"
    proj = line.get("proj")
    if isinstance(proj, dict):
        yield ("proj",), "typeName"
    for kind in ("axiom", "def", "thm", "opaque"):
        declaration = line.get(kind)
        if isinstance(declaration, dict):
            for field in ("name", "all"):
                if field in declaration:
                    yield (kind,), field
    block = line.get("inductive")
    if isinstance(block, dict):
        for group in ("types", "ctors", "recs"):
            items = block.get(group)
            if not isinstance(items, list):
                continue
            for index, item in enumerate(items):
                if not isinstance(item, dict):
                    continue
                site = ("inductive", group, index)
                for field in ("name", "all", "induct", "ctors"):
                    if field in item:
                        yield site, field
                rules = item.get("rules")
                if isinstance(rules, list):
                    for rule_index, rule in enumerate(rules):
                        if isinstance(rule, dict) and "ctor" in rule:
                            yield (*site, "rules", rule_index), "ctor"


def rename_declaration(
    document: Document, line_no: int, path: tuple[object, ...]
) -> Document:
    """Consistently rename one declaration to a fresh, unused simple name."""
    lines = list(document.lines)
    declaration = _declaration(lines, line_no, path)
    old = declaration.get("name")
    if not isinstance(old, int) or isinstance(old, bool) or old == 0:
        raise ValueError("declaration has no interned name")
    users = 0
    for line in lines:
        for kind in ("axiom", "def", "thm", "opaque"):
            payload = line.get(kind)
            if isinstance(payload, dict) and payload.get("name") == old:
                users += 1
        block = line.get("inductive")
        if isinstance(block, dict):
            for group in ("types", "ctors", "recs"):
                items = block.get(group)
                if isinstance(items, list):
                    users += sum(
                        1
                        for item in items
                        if isinstance(item, dict) and item.get("name") == old
                    )
    if users != 1:
        raise ValueError("name is shared by several declarations")

    strings = _name_strings(lines)
    counter = 1
    while f"pyd{counter}" in strings:
        counter += 1
    inserted = {FRESH: "in", "str": {"pre": 0, "str": f"pyd{counter}"}}
    # Constants may reference a name long before its declaration, so the
    # fresh record must precede every remapped reference.  Placing it right
    # after the old name's own record is always early enough, because a
    # well-formed export can only reference names already interned.
    anchor = next(
        (
            index
            for index, line in enumerate(lines)
            if isinstance(line.get("in"), int) and line.get("in") == old
        ),
        None,
    )
    if anchor is None:
        raise ValueError("old name record not found")
    combined = lines[: anchor + 1] + [inserted] + lines[anchor + 1 :]
    try:
        result = _renumber(combined)
    except ValueError as failure:
        raise ValueError(f"document cannot be renumbered: {failure}") from failure
    if result is None:
        raise ValueError("document contains duplicate table identifiers")
    new = result[anchor + 1]["in"]
    for line in result:
        for site_path, field in _rename_sites(line):
            owner = _resolve(line, site_path)
            if owner is None:
                continue
            value = owner.get(field)
            if field == "name" and value == old:
                owner[field] = new
            elif isinstance(value, list):
                owner[field] = [new if item == old else item for item in value]
    return Document(tuple(result))


def _expression_table(lines: list[dict[str, object]]) -> dict[int, dict[str, object]]:
    table: dict[int, dict[str, object]] = {}
    for line in lines:
        declared = declares_table_id(line)
        if declared is not None and declared[0] == "ie":
            table[declared[1]] = line
    return table


def _reachable_from(table: dict[int, dict[str, object]], root: int) -> set[int]:
    reachable: set[int] = set()
    pending = [root]
    while pending:
        identifier = pending.pop()
        if identifier in reachable:
            continue
        line = table.get(identifier)
        if line is None:
            continue
        reachable.add(identifier)
        for site_path, field in expression_reference_sites(line):
            owner = _resolve(line, site_path)
            if owner is None:
                continue
            value = owner.get(field)
            if isinstance(value, int) and not isinstance(value, bool):
                pending.append(value)
    return reachable


def _shared_outside(
    lines: list[dict[str, object]],
    dag: set[int],
    anchor_line: int,
    anchor_path: tuple[object, ...],
    anchor_field: str,
) -> bool:
    """Whether a composite node of the DAG is referenced from outside it.

    The anchor site itself (the declaration's ``value``) is excluded: it is
    the reference the clone rewrites.  Leaf records (sort, bvar, literal)
    are ignored — every declaration's type and value share those, so they
    carry no signal about checker identity or caching, only noise.
    """
    dag_records: set[int] = set()
    table = _expression_table(lines)
    for line_no, line in enumerate(lines):
        declared = declares_table_id(line)
        if declared is not None and declared[0] == "ie" and declared[1] in dag:
            dag_records.add(line_no)

    def composite(identifier: int) -> bool:
        record = table.get(identifier)
        return record is not None and any(
            key in record for key in ("app", "lam", "forallE", "letE", "proj", "mdata")
        )

    for line_no, line in enumerate(lines):
        if line_no in dag_records:
            continue
        for site_path, field in expression_reference_sites(line):
            if line_no == anchor_line and site_path == anchor_path and field == anchor_field:
                continue
            owner = _resolve(line, site_path)
            if owner is None:
                continue
            value = owner.get(field)
            if (
                isinstance(value, int)
                and not isinstance(value, bool)
                and value in dag
                and composite(value)
            ):
                return True
    return False


def clone_value_dag(
    document: Document, line_no: int, path: tuple[object, ...]
) -> Document:
    """Rebuild a declaration's value as a private copy of its expression DAG.

    The clone is structurally identical but no longer shares records with
    any other declaration, so checkers that key caches or hashes on table
    identity see a different presentation of the same term.
    """
    lines = list(document.lines)
    declaration = _declaration(lines, line_no, path)
    root = declaration.get("value")
    if not isinstance(root, int) or isinstance(root, bool):
        raise ValueError("declaration has no value")
    table = _expression_table(lines)
    dag = _reachable_from(table, root)
    if len(dag) < 2 or not _shared_outside(lines, dag, line_no, path, "value"):
        raise ValueError("value DAG is not shared and cloning would be vacuous")
    ordered = sorted(dag)
    local_for = {identifier: -(index + 1) for index, identifier in enumerate(ordered)}
    fragment: list[dict[str, object]] = []
    for identifier in ordered:
        payload = copy.deepcopy(table[identifier])
        payload.pop("ie", None)
        clone = {FRESH: "ie", **payload}
        for site_path, field in expression_reference_sites(clone):
            owner = _resolve(clone, site_path)
            if owner is None:
                continue
            value = owner.get(field)
            if isinstance(value, int) and not isinstance(value, bool) and value in local_for:
                owner[field] = local_for[value]
        fragment.append(clone)
    declaration["value"] = local_for[root]
    result, local = _fragment_with_local_ids(lines, line_no, fragment)
    _fix_local(result, [line_no + len(fragment)], local)
    return Document(tuple(result))


def swap_declarations(document: Document, line_no: int) -> Document:
    """Move a declaration directly after the next declaration in the file.

    A raw two-line swap would drag the moved declaration in front of the
    interned-name and expression records emitted for its successor, which
    breaks the format's backward-reference rule.  Moving only the
    declaration line keeps every table record where it was while still
    reversing the environment order of the two declarations.
    """
    lines = list(document.lines)
    other = next(
        (
            index
            for index in range(line_no + 1, len(lines))
            if is_declaration(lines[index])
        ),
        None,
    )
    if other is None:
        raise ValueError("no later declaration to swap with")
    moved = lines.pop(line_no)
    lines.insert(other, moved)
    return Document(tuple(lines))


def clonable_value(document: Document, line_no: int, path: tuple[object, ...]) -> bool:
    """Whether ``clone_value_dag`` would produce a meaningful, valid result."""
    try:
        lines = list(document.lines)
        declaration = _declaration(lines, line_no, path)
        root = declaration.get("value")
        if not isinstance(root, int) or isinstance(root, bool):
            return False
        table = _expression_table(lines)
        dag = _reachable_from(table, root)
        return len(dag) >= 2 and _shared_outside(lines, dag, line_no, path, "value")
    except ValueError:
        return False


def next_declaration_line(document: Document, line_no: int) -> int | None:
    lines = document.lines
    if not 0 <= line_no < len(lines):
        return None
    return next(
        (index for index in range(line_no + 1, len(lines)) if is_declaration(lines[index])),
        None,
    )


def swap_independent_declarations(document: Document, line_no: int) -> bool:
    """Whether ``swap_declarations`` preserves this document's meaning.

    The swap is safe exactly when neither declaration — including every
    expression record its type, value, and recursor rules reach —
    references a name declared by the other.  Expression, name, and level
    records keep their positions between them, so table references stay
    backward either way.

    Kernel-derived names add one more order sensitivity: processing an
    inductive (or quot) declaration checks and generates auxiliary names
    against the environment as it goes — ``<ind>.rec`` in
    ``check_inductive_types``, ``_nested.*`` for nested inductives — and
    the official kernel rejects a block whose recursor name is already
    taken, exactly like Lean itself.  A swap that changes a declaration's
    position relative to such a block can therefore turn an accepted file
    into a rejected one with no semantic change, so those pairs are
    refused outright.
    """
    from .rewrite import name_reference_sites

    lines = list(document.lines)
    other = next_declaration_line(document, line_no)
    if other is None:
        return False

    table = _expression_table(lines)

    def declared(line: dict[str, object]) -> set[int]:
        names: set[int] = set()
        for kind in ("axiom", "def", "thm", "opaque"):
            payload = line.get(kind)
            if isinstance(payload, dict) and isinstance(payload.get("name"), int):
                names.add(payload["name"])
        block = line.get("inductive")
        if isinstance(block, dict):
            for group in ("types", "ctors", "recs"):
                items = block.get(group)
                if isinstance(items, list):
                    names.update(
                        item["name"]
                        for item in items
                        if isinstance(item, dict) and isinstance(item.get("name"), int)
                    )
        return names

    def plain(line: dict[str, object]) -> bool:
        if any(key in line for key in ("inductive", "quot")):
            return False
        return any(key in line for key in ("axiom", "def", "thm", "opaque"))

    if not plain(lines[line_no]) or not plain(lines[other]):
        return False

    # Names shaped like the ones kernels derive themselves ("_nested.*",
    # "*.rec") are excluded from reordering altogether, as are names we
    # cannot render: predicting every generated name is the kernel's job.
    name_records: dict[int, dict[str, object]] = {}
    for line in lines:
        if isinstance(line.get("in"), int) and isinstance(line.get("str"), dict):
            name_records[line["in"]] = line["str"]

    def aux_shaped(identifier: int) -> bool:
        # Interned names are chains: "Box.rec" is the component "rec"
        # whose prefix names "Box".  Resolve the whole chain and compare
        # with the shapes kernels derive ("_nested.*" prefixes, "rec"
        # suffixes from mk_rec_name).
        components: list[str] = []
        seen: set[int] = set()
        current: object = identifier
        while isinstance(current, int) and not isinstance(current, bool) and current != 0:
            if current in seen:
                return True
            seen.add(current)
            payload = name_records.get(current)
            if not isinstance(payload, dict) or not isinstance(payload.get("str"), str):
                return True  # numeric component: cannot reason, refuse
            components.append(payload["str"])
            current = payload.get("pre")
        if not components:
            return False
        return components[-1] == "_nested" or components[0] == "rec"

    swap_names = declared(lines[line_no]) | declared(lines[other])
    if any(aux_shaped(identifier) for identifier in swap_names):
        return False

    def referenced(line: dict[str, object]) -> set[int]:
        values: set[int] = set()
        records: list[dict[str, object]] = [line]

        def collect(record: dict[str, object]) -> None:
            for path, field in name_reference_sites(record):
                owner = _resolve(record, path)
                if owner is None or field not in owner:
                    continue
                value = owner[field]
                items = value if isinstance(value, list) else [value]
                for item in items:
                    if isinstance(item, int) and not isinstance(item, bool):
                        values.add(item)
                if field in ("str", "num") and isinstance(value, dict):
                    pre = value.get("pre")
                    if isinstance(pre, int) and not isinstance(pre, bool):
                        values.add(pre)

        # Constant references live in expression records, not in the
        # declaration line, so the name closure must follow type, value,
        # and recursor-rule expression DAGs of both declarations.
        roots: list[int] = []
        for kind in ("axiom", "def", "thm", "opaque"):
            payload = line.get(kind)
            if isinstance(payload, dict):
                for field in ("type", "value"):
                    if isinstance(payload.get(field), int):
                        roots.append(payload[field])
        block = line.get("inductive")
        if isinstance(block, dict):
            for group in ("types", "ctors", "recs"):
                items = block.get(group)
                if isinstance(items, list):
                    for item in items:
                        if isinstance(item, dict):
                            if isinstance(item.get("type"), int):
                                roots.append(item["type"])
                            rules = item.get("rules")
                            if isinstance(rules, list):
                                for rule in rules:
                                    if isinstance(rule, dict) and isinstance(rule.get("rhs"), int):
                                        roots.append(rule["rhs"])
        seen: set[int] = set()
        pending = list(roots)
        while pending:
            identifier = pending.pop()
            if identifier in seen:
                continue
            seen.add(identifier)
            record = table.get(identifier)
            if record is None:
                continue
            records.append(record)
            for path, field in expression_reference_sites(record):
                owner = _resolve(record, path)
                if owner is None:
                    continue
                value = owner.get(field)
                if isinstance(value, int) and not isinstance(value, bool):
                    pending.append(value)
        for record in records:
            collect(record)
        return values

    first, second = declared(lines[line_no]), declared(lines[other])
    refs_first, refs_second = referenced(lines[line_no]), referenced(lines[other])
    # Self-references (a recursive declaration) are fine: each line keeps
    # its own payload; only cross-references between the two would break.
    return not (second & refs_first or first & refs_second)


# Checkers key built-in trust on interned names: Lean's kernel and every
# independent checker here resolve the native-reduction extension by name
# (Nat.add, String.append, ...), and Quot primitives are recognized the
# same way.  Renaming such a declaration changes what the checker trusts,
# so the metamorphic-rename oracle must not touch them.  The kernel also
# strips the binder annotations ``outParam``/``optParam``/``autoParam`` by
# name when it generates recursors (renamed, ``HMod.rec`` no longer matches).
SENSITIVE_NAME_ROOTS = frozenset(
    {
        "Nat", "String", "Char", "Quot",
        "Int", "Float", "USize", "ISize",
        "UInt8", "UInt16", "UInt32", "UInt64",
        "Int8", "Int16", "Int32", "Int64",
        "outParam", "optParam", "autoParam",
    }
)


def name_root(document: Document, name_id: int) -> str | None:
    """Resolve the first component of an interned name, or None if numeric."""
    records = {
        line["in"]: line.get("str")
        for line in document.lines
        if isinstance(line.get("in"), int) and isinstance(line.get("str"), dict)
    }
    components: list[str] = []
    seen: set[int] = set()
    current: object = name_id
    while isinstance(current, int) and not isinstance(current, bool) and current != 0:
        if current in seen:
            return None
        seen.add(current)
        payload = records.get(current)
        if not isinstance(payload, dict) or not isinstance(payload.get("str"), str):
            return None
        components.append(payload["str"])
        current = payload.get("pre")
    return components[-1] if components else None


def rename_safe(document: Document, name_id: int) -> bool:
    """Whether renaming this declaration keeps the document's meaning.

    Plain user names are fair game; names rooted at a trusted-primitive
    family are not, and neither are names we cannot render.
    """
    root = name_root(document, name_id)
    return root is not None and root not in SENSITIVE_NAME_ROOTS


# Closed level expressions that normalize to zero.  Records reference each
# other with negative local identifiers; the last record is the disguise.
ZERO_DISGUISES: dict[str, list[dict[str, object]]] = {
    "max-0-0": [{"max": [0, 0]}],
    "imax-0-0": [{"imax": [0, 0]}],
    "imax-1-0": [{"succ": 0}, {"imax": [-1, 0]}],
    "max-imax-1-0": [{"succ": 0}, {"imax": [-1, 0]}, {"max": [-2, 0]}],
    "imax-1-imax-1-0": [{"succ": 0}, {"imax": [-1, 0]}, {"imax": [-1, -2]}],
}


def disguise_prop_sort(
    document: Document, line_no: int, path: tuple[object, ...], field: str, variant: str
) -> Document:
    """Point one ``Sort 0`` reference at a fresh ``Sort l`` with ``l`` closed and zero.

    Only the named reference moves: the shared ``Sort 0`` node keeps serving
    every other use, in particular derived recursor types, which checkers
    compare exactly.  A conforming checker must still see ``Prop`` here —
    the check whose absence was lean4#14613.
    """
    lines = [copy.deepcopy(line) for line in document.lines]
    owner = _resolve(lines[line_no], path)
    if owner is None or not isinstance(owner.get(field), int):
        raise ValueError("rewrite path does not name an expression reference")
    sorts = {line.get("ie"): line for line in lines if "sort" in line}
    if sorts.get(owner[field], {}).get("sort") != 0:
        raise ValueError("rewrite target does not reference Sort 0")
    levels = [{FRESH: "il", **copy.deepcopy(record)} for record in ZERO_DISGUISES[variant]]
    fragment = [*levels, {FRESH: "ie", "sort": -len(levels)}]
    owner[field] = -1
    result = _renumber(lines[:line_no] + fragment + lines[line_no:])
    if result is None:
        raise ValueError("document contains duplicate table identifiers")
    level_ids = {-(index + 1): result[line_no + index]["il"] for index in range(len(levels))}
    for position in range(line_no, line_no + len(levels) + 1):
        _rewrite_references(result[position], {}, {}, level_ids, strict=False)
    disguised = result[line_no + len(levels)]["ie"]
    _rewrite_references(result[line_no + len(fragment)], {-1: disguised}, {}, {}, strict=False)
    return Document(tuple(result))


# Closed level expressions equal to one that a careless normalizer could
# mistake for zero (imax 0 1 is 1, not 0).  Same local-id convention.
NONZERO_IMPOSTORS: dict[str, list[dict[str, object]]] = {
    "imax-0-1": [{"succ": 0}, {"imax": [0, -1]}],
    "max-0-1": [{"succ": 0}, {"max": [0, -1]}],
    "imax-imax-0-0-1": [{"succ": 0}, {"imax": [0, 0]}, {"imax": [-2, -1]}],
    "succ-imax-0-0": [{"imax": [0, 0]}, {"succ": -1}],
    "imax-max-0-0-1": [{"max": [0, 0]}, {"succ": 0}, {"imax": [-1, -2]}],
}


def _declared_name_ids(lines: list[dict[str, object]]) -> dict[str, int]:
    from .rewrite import _declared, _name_strings

    names = _name_strings(lines)
    return {names[name]: name for line in lines for name in _declared(line) if name in names}


def append_prop_impostor(document: Document, variant: str, with_theorem: bool = True) -> Document:
    """Append ``def T : Sort l := Nat`` and ``theorem t : ∀ x y : T, x = y``.

    ``l`` is a closed level equal to one, so ``T`` is not a proposition and
    ``t`` holds only by a proof irrelevance that does not apply.  A checker
    accepting ``t`` normalizes ``l`` to zero; with ``0 = 1`` at ``T`` that is
    a closed proof of ``False``.  Without the theorem the document is valid,
    which separates an impostor bug from incomplete level normalization.
    """
    lines = [copy.deepcopy(line) for line in document.lines]
    declared = _declared_name_ids(lines)
    if not {"Nat", "Eq", "Eq.refl"} <= declared.keys():
        raise ValueError("prop impostor needs Nat, Eq and Eq.refl")
    used = {key: max([0, *(line[key] for line in lines if isinstance(line.get(key), int))]) for key in ("in", "il", "ie")}
    next_in, next_il, next_ie = used["in"] + 1, used["il"] + 1, used["ie"] + 1

    def name(text: str) -> int:
        nonlocal next_in
        lines.append({"in": next_in, "str": {"pre": 0, "str": text}})
        next_in += 1
        return next_in - 1

    def expr(**record: object) -> int:
        nonlocal next_ie
        lines.append({"ie": next_ie, **record})
        next_ie += 1
        return next_ie - 1

    local: dict[int, int] = {}
    for index, record in enumerate(NONZERO_IMPOSTORS[variant]):
        level = {key: (local[value] if isinstance(value, int) and value < 0 else value) for key, value in record.items() if key != "max" and key != "imax"}
        for key in ("max", "imax"):
            if key in record:
                level[key] = [local.get(value, value) for value in record[key]]  # type: ignore[union-attr]
        lines.append({"il": next_il, **level})
        local[-(index + 1)] = next_il
        next_il += 1
    impostor = next_il - 1

    t_name, thm_name, x_name, y_name = (name(text) for text in ("pestycydT", "pestycydImpostor", "x", "y"))
    sort = expr(sort=impostor)
    nat = expr(const={"name": declared["Nat"], "us": []})
    lines.append({"def": {"all": [t_name], "hints": "abbrev", "levelParams": [], "name": t_name, "safety": "safe", "type": sort, "value": nat}})
    if with_theorem:
        t = expr(const={"name": t_name, "us": []})
        x, y = expr(bvar=1), expr(bvar=0)
        eq_t = expr(app={"fn": expr(const={"name": declared["Eq"], "us": [impostor]}), "arg": t})
        body = expr(app={"fn": expr(app={"fn": eq_t, "arg": x}), "arg": y})
        statement = expr(forallE={"binderInfo": "default", "name": x_name, "type": t,
                                  "body": expr(forallE={"binderInfo": "default", "name": y_name, "type": t, "body": body})})
        refl_t = expr(app={"fn": expr(const={"name": declared["Eq.refl"], "us": [impostor]}), "arg": t})
        proof = expr(lam={"binderInfo": "default", "name": x_name, "type": t,
                          "body": expr(lam={"binderInfo": "default", "name": y_name, "type": t,
                                            "body": expr(app={"fn": refl_t, "arg": x})})})
        lines.append({"thm": {"all": [thm_name], "levelParams": [], "name": thm_name, "type": statement, "value": proof}})
    return Document(tuple(lines))


# Single-fault rewrites.  Each breaks exactly one kernel rule in an
# otherwise valid document: a checker missing that one check accepts,
# while one that merely trips over collateral damage cannot hide behind
# a different error.  Mutations that break several rules at once only
# test whether a checker notices *something*.


def let_ill_typed(document: Document, line_no: int, path: tuple[object, ...]) -> Document:
    """Replace ``v`` with ``let x : T := T; v`` for a declaration ``T := v``.

    ``T`` is a type, so the annotation is legal, and ``T : Sort u`` is never
    ``T`` itself; ``v`` is closed and ignores ``x``, so the body and every
    downstream use keep their types.  Only the let-value check fails.
    """
    lines = list(document.lines)
    declaration = _declaration(lines, line_no, path)
    type_id, value_id = declaration.get("type"), declaration.get("value")
    if not isinstance(type_id, int) or not isinstance(value_id, int):
        raise ValueError("declaration needs typed value")
    fragment = [
        {
            FRESH: "ie",
            "letE": {"name": 0, "nondep": True, "type": type_id, "value": type_id, "body": value_id},
        },
    ]
    declaration["value"] = -1
    result, local = _fragment_with_local_ids(lines, line_no, fragment)
    _fix_local(result, [line_no + len(fragment)], local)
    return Document(tuple(result))


def sort_valued_telescope(lines: list[dict[str, object]], root: int) -> bool:
    """Whether expression ``root`` is ``∀ ..., Sort (succ l)``: never a proposition."""
    table = _expression_table(lines)
    levels = {line["il"]: line for line in lines if isinstance(line.get("il"), int)}
    seen = 0
    node = table.get(root)
    while isinstance(node, dict) and isinstance(node.get("forallE"), dict) and seen < 64:
        node = table.get(node["forallE"].get("body"))  # type: ignore[arg-type]
        seen += 1
    if not isinstance(node, dict) or "sort" not in node:
        return False
    level = levels.get(node["sort"])  # type: ignore[arg-type]
    return isinstance(level, dict) and "succ" in level


def theorem_of_type(document: Document, line_no: int) -> Document:
    """Retag ``def d : ∀ ..., Sort (u+1) := v`` as a theorem and cut after it.

    The value still checks against the type; only the rule that a
    theorem states a proposition fails.  Later declarations are cut so a
    checker that does not unfold theorems cannot reject them instead.
    """
    lines = [copy.deepcopy(line) for line in document.lines[: line_no + 1]]
    definition = lines[line_no].get("def")
    if not isinstance(definition, dict) or not sort_valued_telescope(lines, definition.get("type")):  # type: ignore[arg-type]
        raise ValueError("theorem-of-type needs a definition of a type family")
    lines[line_no] = {
        "thm": {key: definition[key] for key in ("all", "levelParams", "name", "type", "value") if key in definition}
    }
    return Document(tuple(lines))


class _Appender:
    """Appends records under fresh table identifiers past every existing one."""

    def __init__(self, lines: list[dict[str, object]]) -> None:
        self.lines = lines
        self.next = {
            key: 1 + max([0, *(line[key] for line in lines if isinstance(line.get(key), int))])
            for key in ("in", "il", "ie")
        }

    def add(self, key: str, **payload: object) -> int:
        identifier = self.next[key]
        self.next[key] += 1
        self.lines.append({key: identifier, **payload})
        return identifier

    def name(self, text: str) -> int:
        # Reuse an existing atom: checkers built on nanoda's tables reject a
        # name bound twice, which would mask the fault being appended.
        for line in self.lines:
            if isinstance(line.get("in"), int) and line.get("str") == {"pre": 0, "str": text}:
                return line["in"]  # type: ignore[return-value]
        return self.add("in", str={"pre": 0, "str": text})

    def pi(self, name: int, domain: int, body: int, implicit: bool = False) -> int:
        info = "implicit" if implicit else "default"
        return self.add("ie", forallE={"binderInfo": info, "name": name, "type": domain, "body": body})

    def lam(self, name: int, domain: int, body: int) -> int:
        return self.add("ie", lam={"binderInfo": "default", "name": name, "type": domain, "body": body})

    def app(self, fn: int, arg: int) -> int:
        return self.add("ie", app={"fn": fn, "arg": arg})


# Declaration-safety faults: the kernel keeps unsafe and partial constants
# out of safe declarations and never unfolds an opaque one.
SAFETY_FAULTS = ("unsafe-in-safe", "unsafe-loop-theorem", "partial-in-safe", "opaque-unfolded")


def append_safety_fault(document: Document, fault: str, control: bool = False) -> Document:
    """Append a constant of restricted safety and a declaration that misuses it.

    With ``F := ∀ p : Prop, p`` (a closed falsehood) and ``T := ∀ p : Prop, p → p``:

    - ``unsafe-in-safe``: ``unsafe def k : Prop := F``, then ``def use : Prop := k``;
    - ``unsafe-loop-theorem``: ``unsafe def k : F := k``, then ``theorem use : F := k``,
      a closed proof of ``False`` if a checker lets it through;
    - ``partial-in-safe``: as ``unsafe-in-safe`` with ``k`` partial;
    - ``opaque-unfolded``: ``opaque k : Prop := T``, then ``theorem use : k := fun p h => h``,
      which typechecks only by unfolding ``k``.

    ``control`` keeps the shape and lifts the one restriction: ``use`` becomes
    unsafe (``k`` becomes a plain definition for ``opaque-unfolded``).  Partial
    definitions may recur like unsafe ones (``partial def k : F := k`` is
    accepted), so recursion alone is no fault.
    """
    if fault not in SAFETY_FAULTS:
        raise ValueError(f"unknown safety fault: {fault}")
    lines = [copy.deepcopy(line) for line in document.lines]
    out = _Appender(lines)
    k_name = out.name("pestycydRestricted")
    use_name = out.name("pestycydUse")
    p_name, h_name = out.name("p"), out.name("h")
    prop = out.add("ie", sort=0)
    b0, b1 = out.add("ie", bvar=0), out.add("ie", bvar=1)
    false_ = out.pi(p_name, prop, b0)
    k = out.add("ie", const={"name": k_name, "us": []})

    def definition(name: int, type_: int, value: int, safety: str) -> dict[str, object]:
        return {"def": {"all": [name], "hints": "opaque", "levelParams": [], "name": name,
                        "safety": safety, "type": type_, "value": value}}

    if fault in ("unsafe-in-safe", "partial-in-safe"):
        restricted = "unsafe" if fault == "unsafe-in-safe" else "partial"
        lines.append(definition(k_name, prop, false_, restricted))
        lines.append(definition(use_name, prop, k, "unsafe" if control else "safe"))
    elif fault == "unsafe-loop-theorem":
        lines.append(definition(k_name, false_, k, "unsafe"))
        if control:
            lines.append(definition(use_name, false_, k, "unsafe"))
        else:
            lines.append({"thm": {"all": [use_name], "levelParams": [], "name": use_name, "type": false_, "value": k}})
    else:
        true_ = out.pi(p_name, prop, out.pi(h_name, b0, b1))
        proof = out.lam(p_name, prop, out.lam(h_name, b0, b0))
        if control:
            lines.append(definition(k_name, prop, true_, "safe"))
        else:
            lines.append({"opaque": {"all": [k_name], "isUnsafe": False, "levelParams": [], "name": k_name,
                                     "type": prop, "value": true_}})
        lines.append({"thm": {"all": [use_name], "levelParams": [], "name": use_name, "type": k, "value": proof}})
    return Document(tuple(lines))


def append_index_elimination(document: Document, control: bool = False) -> Document:
    """Append ``Q : Prop → Prop`` with a large recursor, then use it at ``Type``.

    A proposition eliminates into every universe when each constructor
    field that is not a proof is itself an index of the constructor's
    result, as in ``Eq``.  ``control`` is ``mk : (x : Prop) → Q x``; the
    fault is ``mk : (x : Prop) → Q (x → x)``, where ``x`` only occurs
    inside an index, so only the small recursor is derivable and
    ``use := fun a t => Q.rec (fun _ _ => Type) (fun _ => Prop) t`` needs
    the forged large one.
    """
    lines = [copy.deepcopy(line) for line in document.lines]
    out = _Appender(lines)
    q_name = out.name("PestycydIndexed")
    mk_name = out.add("in", str={"pre": q_name, "str": "mk"})
    rec_name = out.add("in", str={"pre": q_name, "str": "rec"})
    use_name = out.add("in", str={"pre": q_name, "str": "use"})
    u_name, motive_name, a_name, t_name, x_name, h_name = (
        out.name(text) for text in ("u", "motive", "a", "t", "x", "h")
    )
    one = out.add("il", succ=0)
    two = out.add("il", succ=one)
    u = out.add("il", param=u_name)
    prop, type_, sort_u = out.add("ie", sort=0), out.add("ie", sort=one), out.add("ie", sort=u)
    b0, b1, b3 = out.add("ie", bvar=0), out.add("ie", bvar=1), out.add("ie", bvar=3)
    q = out.add("ie", const={"name": q_name, "us": []})
    mk = out.add("ie", const={"name": mk_name, "us": []})
    # The index of ``mk x`` with ``x`` bound at 0.
    index = b0 if control else out.pi(h_name, b0, b1)
    q_type = out.pi(a_name, prop, prop)
    ctor_type = out.pi(x_name, prop, out.app(q, index))
    motive_type = out.pi(a_name, prop, out.pi(t_name, out.app(q, b0), sort_u))
    # Under motive: ∀ (x : Prop), motive (index x) (mk x).
    minor = out.pi(x_name, prop, out.app(out.app(b1, index), out.app(mk, b0)))
    # ∀ {motive} (mk : minor) {a : Prop} (t : Q a), motive a t.
    rec_type = out.pi(motive_name, motive_type, out.pi(mk_name, minor, out.pi(
        a_name, prop, out.pi(t_name, out.app(q, b0), out.app(out.app(b3, b1), b0)), implicit=True)), implicit=True)
    rhs = out.lam(motive_name, motive_type, out.lam(mk_name, minor, out.lam(x_name, prop, out.app(b1, b0))))
    lines.append({"inductive": {
        "types": [{"all": [q_name], "ctors": [mk_name], "isRec": False, "isReflexive": False, "isUnsafe": False,
                   "levelParams": [], "name": q_name, "numIndices": 1, "numNested": 0, "numParams": 0,
                   "type": q_type}],
        "ctors": [{"cidx": 0, "induct": q_name, "isUnsafe": False, "levelParams": [], "name": mk_name,
                   "numFields": 1, "numParams": 0, "type": ctor_type}],
        "recs": [{"all": [q_name], "isUnsafe": False, "k": False, "levelParams": [u_name], "name": rec_name,
                  "numIndices": 1, "numMinors": 1, "numMotives": 1, "numParams": 0,
                  "rules": [{"ctor": mk_name, "nfields": 1, "rhs": rhs}], "type": rec_type}],
    }})
    # use := fun (a : Prop) (t : Q a) => @Q.rec.{2} (fun _ _ => Type) (fun _ => Prop) a t.
    motive = out.lam(a_name, prop, out.lam(t_name, out.app(q, b0), type_))
    term = out.app(out.app(out.add("ie", const={"name": rec_name, "us": [two]}), motive), out.lam(x_name, prop, prop))
    value = out.lam(a_name, prop, out.lam(t_name, out.app(q, b0), out.app(out.app(term, b1), b0)))
    lines.append({"def": {"all": [use_name], "hints": "abbrev", "levelParams": [], "name": use_name,
                          "safety": "safe", "type": out.pi(a_name, prop, out.pi(t_name, out.app(q, b0), type_)),
                          "value": value}})
    return Document(tuple(lines))


def append_undeclared_universe(document: Document) -> Document:
    """Append ``def k.{v} : Type := Prop`` and ``def bad : Type := k.{u}``.

    ``k``'s type ignores its universe, so ``k.{u}`` has type ``Type`` for
    any ``u``: the only fault is that ``bad`` binds no ``u``.
    """
    lines = [copy.deepcopy(line) for line in document.lines]
    out = _Appender(lines)
    k_name = out.name("pestycydUniverseFree")
    bad_name = out.name("pestycydUndeclaredUniverse")
    v_name, u_name = out.name("v"), out.name("u")
    one = out.add("il", succ=0)
    out.add("il", param=v_name)  # exporters emit a level for every declared parameter
    u = out.add("il", param=u_name)
    prop, type_ = out.add("ie", sort=0), out.add("ie", sort=one)
    lines.append({"def": {"all": [k_name], "hints": "abbrev", "levelParams": [v_name], "name": k_name,
                          "safety": "safe", "type": type_, "value": prop}})
    use = out.add("ie", const={"name": k_name, "us": [u]})
    lines.append({"def": {"all": [bad_name], "hints": "abbrev", "levelParams": [], "name": bad_name,
                          "safety": "safe", "type": type_, "value": use}})
    return Document(tuple(lines))


def extra_recursor(document: Document, line_no: int) -> Document:
    """Serialize a copy of a block's first recursor under a name of its own.

    The copy is a faithful recursor of the block, so its type and rules
    check; the only fault is a recursor the block does not generate, which
    a checker that installs serialized recursors without matching their
    names would add to the environment (nanoda PR #65).
    """
    from .rewrite import renumber

    lines = [copy.deepcopy(line) for line in document.lines]
    block = lines[line_no].get("inductive")
    if not isinstance(block, dict) or not block.get("recs"):
        raise ValueError("extra-recursor needs an inductive block with a recursor")
    original = block["recs"][0]
    fresh = 1 + max([0, *(line["in"] for line in lines if isinstance(line.get("in"), int))])
    copy_rec = copy.deepcopy(original)
    copy_rec["name"] = fresh
    block["recs"].append(copy_rec)
    lines.insert(line_no, {"in": fresh, "str": {"pre": original["name"], "str": "pestycydCopy"}})
    renumbered = renumber(Document(tuple(lines)))
    if renumbered is None:
        raise ValueError("document has dangling or re-bound table references")
    return renumbered


# Field types for append_field_inductive: the one rule each breaks.
FIELD_FAULTS = ("non-positive", "field-too-large", "control")


def append_field_inductive(document: Document, fault: str) -> Document:
    """Append ``inductive I : Type | mk : F → I`` with its exact recursor.

    ``F`` is ``I → Prop`` (a non-positive occurrence), ``Type`` (a field
    in a universe above the type's), or ``Prop`` for the valid control.
    ``F`` never ends in ``I``, so the field is non-recursive and the
    serialized recursor is the one a checker missing the broken rule
    derives: positivity or the universe bound is the only fault.
    ``isRec`` follows whether a field mentions ``I``, which is how checkers
    that validate it (rather than derive it) compute the flag.
    """
    if fault not in FIELD_FAULTS:
        raise ValueError(f"unknown field fault: {fault}")
    lines = [copy.deepcopy(line) for line in document.lines]
    out = _Appender(lines)
    stem = {"non-positive": "Neg", "field-too-large": "Big", "control": "Ok"}[fault]
    i_name = out.name(f"Pestycyd{stem}")
    mk_name = out.add("in", str={"pre": i_name, "str": "mk"})
    rec_name = out.add("in", str={"pre": i_name, "str": "rec"})
    u_name, motive_name, t_name, a_name = (out.name(text) for text in ("u", "motive", "t", "a"))
    one = out.add("il", succ=0)
    u = out.add("il", param=u_name)
    prop, type_, sort_u = out.add("ie", sort=0), out.add("ie", sort=one), out.add("ie", sort=u)
    i = out.add("ie", const={"name": i_name, "us": []})
    mk = out.add("ie", const={"name": mk_name, "us": []})
    field = {"non-positive": lambda: out.pi(t_name, i, prop), "field-too-large": lambda: type_,
             "control": lambda: prop}[fault]()
    b0, b1, b2 = (out.add("ie", bvar=index) for index in range(3))
    ctor_type = out.pi(a_name, field, i)
    motive_type = out.pi(t_name, i, sort_u)
    # Under motive: ∀ (a : F), motive (mk a).
    minor = out.pi(a_name, field, out.app(b1, out.app(mk, b0)))
    # ∀ {motive}, ∀ (mk : minor), ∀ (t : I), motive t.
    rec_type = out.pi(motive_name, motive_type, out.pi(mk_name, minor, out.pi(t_name, i, out.app(b2, b0))), implicit=True)
    # fun motive mk a => mk a.
    rhs = out.lam(motive_name, motive_type, out.lam(mk_name, minor, out.lam(a_name, field, out.app(b1, b0))))
    lines.append({"inductive": {
        "types": [{"all": [i_name], "ctors": [mk_name], "isRec": fault == "non-positive", "isReflexive": False, "isUnsafe": False,
                   "levelParams": [], "name": i_name, "numIndices": 0, "numNested": 0, "numParams": 0,
                   "type": type_}],
        "ctors": [{"cidx": 0, "induct": i_name, "isUnsafe": False, "levelParams": [], "name": mk_name,
                   "numFields": 1, "numParams": 0, "type": ctor_type}],
        "recs": [{"all": [i_name], "isUnsafe": False, "k": False, "levelParams": [u_name], "name": rec_name,
                  "numIndices": 0, "numMinors": 1, "numMotives": 1, "numParams": 0,
                  "rules": [{"ctor": mk_name, "nfields": 1, "rhs": rhs}], "type": rec_type}],
    }})
    return Document(tuple(lines))


# Where append_undeclared_inductive puts the unbound universe ``u``.
UNDECLARED_INDUCTIVE_SITES = ("type", "ctor")


def append_undeclared_inductive(document: Document, site: str, declared: bool = False) -> Document:
    """Append an inductive block whose types mention a universe ``u``.

    ``type``: ``inductive U : Sort (u+1) | mk : U`` with its large recursor.
    ``ctor``: ``inductive I : Prop | mk : Sort u → I`` with its small one;
    the type is closed, so only the constructor (and the recursor it
    induces) mention ``u``.  Without ``declared`` no member of the block
    binds ``u``, which is the only fault (nanoda checks inductive blocks
    without the declaration's universe parameters); with it the block is
    the valid control ``U.{u}`` / ``I.{u}``.
    """
    if site not in UNDECLARED_INDUCTIVE_SITES:
        raise ValueError(f"unknown undeclared-universe site: {site}")
    lines = [copy.deepcopy(line) for line in document.lines]
    out = _Appender(lines)
    i_name = out.name("PestycydUnbound" + ("Type" if site == "type" else "Ctor"))
    mk_name = out.add("in", str={"pre": i_name, "str": "mk"})
    rec_name = out.add("in", str={"pre": i_name, "str": "rec"})
    # Lean names the elimination level ``u_1`` when the block already uses ``u``.
    u_name, w_name, motive_name, t_name, a_name = (out.name(text) for text in ("u", "u_1", "motive", "t", "a"))
    u = out.add("il", param=u_name)
    params = [u_name] if declared else []
    us = [u] if declared else []
    i = out.add("ie", const={"name": i_name, "us": us})
    mk = out.add("ie", const={"name": mk_name, "us": us})
    b0, b1, b2 = (out.add("ie", bvar=index) for index in range(3))
    if site == "type":
        w = out.add("il", param=w_name)
        i_type, ctor_type = out.add("ie", sort=out.add("il", succ=u)), i
        motive_type = out.pi(t_name, i, out.add("ie", sort=w))
        minor = out.app(b0, mk)
        # fun motive mk => mk.
        rhs = out.lam(motive_name, motive_type, out.lam(mk_name, minor, b0))
        fields, rec_params = 0, [w_name, *params]
    else:
        sort_u = out.add("ie", sort=u)
        i_type, ctor_type = out.add("ie", sort=0), out.pi(a_name, sort_u, i)
        motive_type = out.pi(t_name, i, i_type)
        # Under motive: ∀ (a : Sort u), motive (mk a).
        minor = out.pi(a_name, sort_u, out.app(b1, out.app(mk, b0)))
        # fun motive mk a => mk a.
        rhs = out.lam(motive_name, motive_type, out.lam(mk_name, minor, out.lam(a_name, sort_u, out.app(b1, b0))))
        fields, rec_params = 1, params
    # ∀ {motive}, ∀ (mk : minor), ∀ (t : I), motive t.
    rec_type = out.pi(motive_name, motive_type, out.pi(mk_name, minor, out.pi(t_name, i, out.app(b2, b0))), implicit=True)
    lines.append({"inductive": {
        "types": [{"all": [i_name], "ctors": [mk_name], "isRec": False, "isReflexive": False, "isUnsafe": False,
                   "levelParams": params, "name": i_name, "numIndices": 0, "numNested": 0, "numParams": 0,
                   "type": i_type}],
        "ctors": [{"cidx": 0, "induct": i_name, "isUnsafe": False, "levelParams": params, "name": mk_name,
                   "numFields": fields, "numParams": 0, "type": ctor_type}],
        "recs": [{"all": [i_name], "isUnsafe": False, "k": False, "levelParams": rec_params, "name": rec_name,
                  "numIndices": 0, "numMinors": 1, "numMotives": 1, "numParams": 0,
                  "rules": [{"ctor": mk_name, "nfields": fields, "rhs": rhs}], "type": rec_type}],
    }})
    return Document(tuple(lines))


# Propositions serialized with a large eliminator, and what each breaks.
LARGE_ELIMINATION = ("two-ctors", "data-field", "control")


def append_large_elimination(document: Document, variant: str) -> Document:
    """Append a proposition ``P`` with a large recursor, then use it at ``Type``.

    A proposition eliminates into every universe only with at most one
    constructor whose fields are proofs.  ``two-ctors`` (like ``Or``) and
    ``data-field`` (``mk : Prop → P``) break that; ``control`` (like
    ``True``) is valid.  The serialized ``P.rec`` is the large one, and
    ``def use : P → Type := fun t => P.rec (fun _ => Type) ... t`` needs it,
    so a checker that derives the small eliminator still rejects ``use``:
    accepting both means a forged eliminator was installed, and with two
    constructors proof irrelevance then proves ``False``.
    """
    if variant not in LARGE_ELIMINATION:
        raise ValueError(f"unknown large-elimination variant: {variant}")
    lines = [copy.deepcopy(line) for line in document.lines]
    out = _Appender(lines)
    stem = {"two-ctors": "Either", "data-field": "Holds", "control": "Unit"}[variant]
    p_name = out.name(f"Pestycyd{stem}")
    ctor_names = [out.add("in", str={"pre": p_name, "str": text})
                  for text in (("a", "b") if variant == "two-ctors" else ("mk",))]
    rec_name = out.add("in", str={"pre": p_name, "str": "rec"})
    use_name = out.add("in", str={"pre": p_name, "str": "use"})
    u_name, motive_name, t_name, x_name = (out.name(text) for text in ("u", "motive", "t", "x"))
    one = out.add("il", succ=0)
    two = out.add("il", succ=one)
    u = out.add("il", param=u_name)
    prop, type_, sort_u = out.add("ie", sort=0), out.add("ie", sort=one), out.add("ie", sort=u)
    bvars: dict[int, int] = {}

    def bvar(index: int) -> int:
        if index not in bvars:
            bvars[index] = out.add("ie", bvar=index)
        return bvars[index]

    p = out.add("ie", const={"name": p_name, "us": []})
    ctors = [out.add("ie", const={"name": name, "us": []}) for name in ctor_names]
    field = prop if variant == "data-field" else None
    count = len(ctors)
    motive_type = out.pi(t_name, p, sort_u)
    minors = []
    for index, ctor in enumerate(ctors):
        # Inside minor ``index`` the motive is bound ``index`` binders out.
        if field is None:
            minors.append(out.app(bvar(index), ctor))
        else:
            minors.append(out.pi(x_name, field, out.app(bvar(index + 1), out.app(ctor, bvar(0)))))
    body = out.pi(t_name, p, out.app(bvar(count + 1), bvar(0)))
    for index in reversed(range(count)):
        body = out.pi(ctor_names[index], minors[index], body)
    rec_type = out.pi(motive_name, motive_type, body, implicit=True)
    rules = []
    for index, ctor_name in enumerate(ctor_names):
        if field is None:
            rhs = bvar(count - 1 - index)
        else:
            rhs = out.lam(x_name, field, out.app(bvar(count - index), bvar(0)))
        for binder in reversed(range(count)):
            rhs = out.lam(ctor_names[binder], minors[binder], rhs)
        rhs = out.lam(motive_name, motive_type, rhs)
        rules.append({"ctor": ctor_name, "nfields": 0 if field is None else 1, "rhs": rhs})
    lines.append({"inductive": {
        "types": [{"all": [p_name], "ctors": ctor_names, "isRec": False, "isReflexive": False, "isUnsafe": False,
                   "levelParams": [], "name": p_name, "numIndices": 0, "numNested": 0, "numParams": 0,
                   "type": prop}],
        "ctors": [{"cidx": index, "induct": p_name, "isUnsafe": False, "levelParams": [], "name": name,
                   "numFields": 0 if field is None else 1, "numParams": 0,
                   "type": p if field is None else out.pi(x_name, field, p)}
                  for index, name in enumerate(ctor_names)],
        "recs": [{"all": [p_name], "isUnsafe": False, "k": variant == "control", "levelParams": [u_name],
                  "name": rec_name, "numIndices": 0, "numMinors": count, "numMotives": 1, "numParams": 0,
                  "rules": rules, "type": rec_type}],
    }})
    # use := fun t : P => @P.rec.{2} (fun _ => Type) m... t, each m returning Prop.
    term = out.app(out.add("ie", const={"name": rec_name, "us": [two]}), out.lam(t_name, p, type_))
    for _ in ctors:
        term = out.app(term, prop if field is None else out.lam(x_name, field, prop))
    value = out.lam(t_name, p, out.app(term, bvar(0)))
    lines.append({"def": {"all": [use_name], "hints": "abbrev", "levelParams": [], "name": use_name,
                          "safety": "safe", "type": out.pi(t_name, p, type_), "value": value}})
    return Document(tuple(lines))


def _shared(document: Document) -> Document:
    """Merge the records a rewrite re-interned (``bvar 0``, ``Sort 0``, ...).

    Nanoda-family checkers refuse a repeated record before checking
    anything, which would mask the fault (or, for a metamorphic wrap, the
    acceptance) under test.  ``clone-value-dag`` is the exception: its
    duplicates are the point.
    """
    return share(document) or document


def apply_rewrite(document: Document, rewrite: Rewrite) -> Document:
    lines = [copy.deepcopy(line) for line in document.lines]
    if not 0 <= rewrite.line < len(lines):
        raise ValueError("rewrite lies outside the document")
    kind = rewrite.kind
    if kind == "wrap-beta":
        return _shared(wrap_beta(Document(tuple(lines)), rewrite.line, tuple(rewrite.path)))
    if kind == "wrap-eta":
        return _shared(wrap_eta(Document(tuple(lines)), rewrite.line, tuple(rewrite.path)))
    if kind == "wrap-let":
        return _shared(wrap_let(Document(tuple(lines)), rewrite.line, tuple(rewrite.path)))
    if kind == "rename-declaration":
        return rename_declaration(Document(tuple(lines)), rewrite.line, tuple(rewrite.path))
    if kind == "clone-value-dag":
        return clone_value_dag(Document(tuple(lines)), rewrite.line, tuple(rewrite.path))
    if kind == "swap-declarations":
        return swap_declarations(Document(tuple(lines)), rewrite.line)
    if kind == "let-ill-typed":
        return let_ill_typed(Document(tuple(lines)), rewrite.line, tuple(rewrite.path))
    if kind == "theorem-of-type":
        return theorem_of_type(Document(tuple(lines)), rewrite.line)
    if kind == "append-large-elimination":
        return _shared(append_large_elimination(Document(tuple(lines)), str(rewrite.params[0])))
    if kind == "extra-recursor":
        return extra_recursor(Document(tuple(lines)), rewrite.line)
    if kind == "append-field-inductive":
        return _shared(append_field_inductive(Document(tuple(lines)), str(rewrite.params[0])))
    if kind == "append-undeclared-universe":
        return _shared(append_undeclared_universe(Document(tuple(lines))))
    if kind == "append-undeclared-inductive":
        return _shared(append_undeclared_inductive(Document(tuple(lines)), str(rewrite.params[0])))
    if kind == "append-safety-fault":
        return _shared(append_safety_fault(Document(tuple(lines)), str(rewrite.params[0])))
    if kind == "append-index-elimination":
        return _shared(append_index_elimination(Document(tuple(lines))))
    if kind == "append-prop-impostor":
        return _shared(append_prop_impostor(Document(tuple(lines)), str(rewrite.params[0])))
    if kind == "disguise-prop-sort":
        field, variant = rewrite.params
        return disguise_prop_sort(
            Document(tuple(lines)), rewrite.line, tuple(rewrite.path), str(field), str(variant)
        )
    raise ValueError(f"unknown rewrite kind: {kind}")
