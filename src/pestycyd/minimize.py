from __future__ import annotations

import json
from collections.abc import Callable


def well_formed_export(lines: list[str]) -> bool:
    """Check lean4export back-references without making a kernel judgment."""
    try:
        rows = [json.loads(line) for line in lines if line.strip()]
    except (TypeError, ValueError, json.JSONDecodeError):
        return False
    if not rows or any(not isinstance(row, dict) for row in rows):
        return False
    if "meta" not in rows[0] or sum("meta" in row for row in rows) != 1:
        return False

    names = {0}
    levels = {0}
    expressions: set[int] = set()
    next_name = 1
    next_level = 1
    next_expression = 0
    declarations = 0

    def known(values: object, table: set[int]) -> bool:
        return isinstance(values, list) and all(
            isinstance(value, int) and value in table for value in values
        )

    def name(value: object) -> bool:
        return isinstance(value, int) and value in names

    def level(value: object) -> bool:
        return isinstance(value, int) and value in levels

    def expression(value: object) -> bool:
        return isinstance(value, int) and value in expressions

    def expression_record(row: dict[str, object]) -> bool:
        if "sort" in row:
            return level(row["sort"])
        if "bvar" in row or "lit" in row or "natVal" in row or "strLit" in row or "strVal" in row:
            return True
        const = row.get("const")
        if isinstance(const, dict):
            return name(const.get("name")) and known(const.get("us"), levels)
        app = row.get("app")
        if isinstance(app, dict):
            return expression(app.get("fn")) and expression(app.get("arg"))
        for key in ("lam", "forallE"):
            binder = row.get(key)
            if isinstance(binder, dict):
                return (
                    name(binder.get("name"))
                    and expression(binder.get("type"))
                    and expression(binder.get("body"))
                )
        let_expr = row.get("letE")
        if isinstance(let_expr, dict):
            return (
                name(let_expr.get("name"))
                and expression(let_expr.get("type"))
                and expression(let_expr.get("value"))
                and expression(let_expr.get("body"))
            )
        proj = row.get("proj")
        if isinstance(proj, dict):
            return name(proj.get("typeName")) and expression(proj.get("struct"))
        mdata = row.get("mdata")
        if isinstance(mdata, dict):
            return expression(mdata.get("expr"))
        return False

    def declar_info(info: object, *, has_value: bool) -> bool:
        if not isinstance(info, dict):
            return False
        return (
            name(info.get("name"))
            and known(info.get("levelParams"), names)
            and expression(info.get("type"))
            and (not has_value or expression(info.get("value")))
        )

    def inductive(block: object) -> bool:
        if not isinstance(block, dict):
            return False
        for typ in block.get("types", []):
            if not isinstance(typ, dict):
                return False
            if not name(typ.get("name")) or not expression(typ.get("type")):
                return False
            if not known(typ.get("levelParams"), names):
                return False
            if not known(typ.get("all"), names) or not known(typ.get("ctors"), names):
                return False
        for ctor in block.get("ctors", []):
            if not isinstance(ctor, dict):
                return False
            if not name(ctor.get("name")) or not name(ctor.get("induct")):
                return False
            if not expression(ctor.get("type")) or not known(ctor.get("levelParams"), names):
                return False
        for rec in block.get("recs", []):
            if not isinstance(rec, dict):
                return False
            if not name(rec.get("name")) or not expression(rec.get("type")):
                return False
            if not known(rec.get("levelParams"), names) or not known(rec.get("all"), names):
                return False
            for rule in rec.get("rules", []):
                if not isinstance(rule, dict):
                    return False
                if not name(rule.get("ctor")) or not expression(rule.get("rhs")):
                    return False
        return True

    for row in rows:
        if "in" in row:
            identifier = row["in"]
            if identifier != next_name:
                return False
            payload = row.get("str", row.get("num"))
            if not isinstance(payload, dict) or not name(payload.get("pre")):
                return False
            names.add(identifier)
            next_name += 1
            continue
        if "il" in row:
            identifier = row["il"]
            if identifier != next_level:
                return False
            if "param" in row and not name(row["param"]):
                return False
            if "succ" in row and not level(row["succ"]):
                return False
            for key in ("max", "imax"):
                if key in row and not known(row[key], levels):
                    return False
            levels.add(identifier)
            next_level += 1
            continue
        if "ie" in row:
            identifier = row["ie"]
            if identifier != next_expression or not expression_record(row):
                return False
            expressions.add(identifier)
            next_expression += 1
            continue
        if "meta" in row:
            continue
        if "axiom" in row:
            valid = declar_info(row["axiom"], has_value=False)
        elif "def" in row:
            valid = declar_info(row["def"], has_value=True)
        elif "opaque" in row:
            valid = declar_info(row["opaque"], has_value=True)
        elif "thm" in row:
            valid = declar_info(row["thm"], has_value=True)
        elif "inductive" in row:
            valid = inductive(row["inductive"])
        elif "quot" in row:
            valid = isinstance(row["quot"], dict)
        else:
            return False
        if not valid:
            return False
        declarations += 1
    return declarations > 0


def ddmin(lines: list[str], interesting: Callable[[list[str]], bool], keep: tuple[str, ...] = ()) -> list[str]:
    current = list(lines)
    groups = 2
    while True:
        removable = [
            index for index, line in enumerate(current)
            if not any(marker in line for marker in keep)
        ]
        if not removable:
            return current
        width = max(1, (len(removable) + groups - 1) // groups)
        reduced = False
        for start in range(0, len(removable), width):
            removed = set(removable[start : start + width])
            trial = [line for index, line in enumerate(current) if index not in removed]
            if trial and interesting(trial):
                current = trial
                groups = 2
                reduced = True
                break
        if reduced:
            continue
        if groups >= len(removable):
            return current
        groups = min(len(removable), groups * 2)

