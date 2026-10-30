"""Known-divergence rules: label findings whose every deviation is explained.

A hunt saves any input on which checkers disagree with the oracle or with
each other.  Most such disagreements are long understood — a checker that
derives a field instead of reading it, a resource budget, a feature it
declines by design — and re-reading them after every hunt buries the one
case that is new.  ``triage.toml`` records those classes as rules:

    [[rule]]
    id = "con-derived-recursor-rules"
    why = "con-* derive recursor rules and ignore serialized rules[].rhs"
    kernels = ["con-leche", "con-ron"]
    status = ["accept"]
    expected = ["reject"]                       # optional
    campaigns = ["recursor-crosswire"]          # optional, fnmatch
    labels = ["*rules*"]                        # optional, fnmatch
    output = "regex searched in the output"     # optional
    sites = ["inductive.recs*"]                 # optional, fnmatch
    reference = "Invalid recursor"              # optional, regex on official's output

``sites`` names where the mutation lands: the declaration field it edits
(``inductive.recs.rules.rhs``), or for an edited table record every
declaration field that reaches it (``def.value``; ``unreachable`` when
none does).  A rule with ``sites`` applies only when all of them match,
which tells "only a recursor rule changed" from "a definition changed".
``reference`` matches the reference checker's own reason, for classes
defined by *why* the input is wrong rather than where it was edited.

Each finding gets an expected verdict (the oracle's, else official's,
else the plurality's).  A kernel *deviates* when its status differs; a
rule *explains* a deviating kernel when every given field matches.  The
finding is *known* when each deviation has an explanation; anything left
over is what deserves a human.
"""

from __future__ import annotations

import fnmatch
import re
import tomllib
from collections import Counter, defaultdict
from dataclasses import dataclass
from pathlib import Path
from typing import Iterator, Mapping, Sequence

from .rewrite import (
    _resolve,
    declares_table_id,
    expression_reference_sites,
    level_reference_sites,
    name_reference_sites,
)

REFERENCE_KERNEL = "official"
BUILTIN_RULES = Path(__file__).with_name("triage.toml")
DECLARATION_ROOTS = frozenset({"axiom", "def", "thm", "opaque", "quot", "inductive"})


@dataclass(frozen=True)
class Rule:
    id: str
    why: str
    kernels: tuple[str, ...]
    statuses: tuple[str, ...]
    expected: tuple[str, ...] = ()
    campaigns: tuple[str, ...] = ()
    labels: tuple[str, ...] = ()
    output: re.Pattern[str] | None = None
    sites: tuple[str, ...] = ()
    reference: re.Pattern[str] | None = None

    def explains(self, kernel: str, status: str, output: str, case: "Case") -> bool:
        return (
            _any_match(kernel, self.kernels)
            and status in self.statuses
            and (not self.expected or case.expected in self.expected)
            and (not self.campaigns or _any_match(case.campaign, self.campaigns))
            and (not self.labels or _any_match(case.label, self.labels))
            and (self.output is None or self.output.search(output) is not None)
            and (not self.sites or bool(case.sites) and all(_any_match(s, self.sites) for s in case.sites))
            and (self.reference is None or self.reference.search(case.reference) is not None)
        )


def _any_match(value: str, patterns: tuple[str, ...]) -> bool:
    return any(fnmatch.fnmatchcase(value, pattern) for pattern in patterns)


@dataclass(frozen=True)
class Case:
    """What a rule may look at besides the deviating kernel itself."""

    campaign: str
    label: str
    expected: str
    sites: frozenset[str] = frozenset()
    reference: str = ""


@dataclass(frozen=True)
class Triage:
    expected: str
    explained: Mapping[str, str]
    unexplained: tuple[str, ...]

    @property
    def known(self) -> bool:
        return bool(self.explained) and not self.unexplained

    @property
    def rule_ids(self) -> tuple[str, ...]:
        return tuple(sorted(set(self.explained.values())))

    def json(self) -> dict[str, object]:
        return {
            "expected": self.expected,
            "known": self.known,
            "explained": dict(sorted(self.explained.items())),
            "unexplained": list(self.unexplained),
        }


def _strings(value: object, where: str, required: bool = False) -> tuple[str, ...]:
    if value is None and not required:
        return ()
    if isinstance(value, str):
        value = [value]
    if not isinstance(value, list) or not value or not all(isinstance(item, str) for item in value):
        raise ValueError(f"{where} must be a string or a non-empty string array")
    return tuple(value)


def load_rules(path: Path) -> tuple[Rule, ...]:
    with path.open("rb") as stream:
        raw = tomllib.load(stream)
    tables = raw.get("rule", [])
    if not isinstance(tables, list):
        raise ValueError(f"{path}: [[rule]] must be an array of tables")
    rules: list[Rule] = []
    seen: set[str] = set()
    for table in tables:
        if not isinstance(table, dict):
            raise ValueError(f"{path}: invalid [[rule]] table")
        rule_id = table.get("id")
        if not isinstance(rule_id, str) or not rule_id or rule_id in seen:
            raise ValueError(f"{path}: every rule needs a unique string id")
        seen.add(rule_id)
        where = f"{path}: rule {rule_id}"
        unknown = set(table).difference(
            {"id", "why", "kernels", "status", "expected", "campaigns", "labels", "output", "sites", "reference"}
        )
        if unknown:
            raise ValueError(f"{where}: unknown keys {', '.join(sorted(unknown))}")
        why = table.get("why", "")
        output, reference = table.get("output"), table.get("reference")
        if not isinstance(why, str) or not all(v is None or isinstance(v, str) for v in (output, reference)):
            raise ValueError(f"{where}: why, output and reference must be strings")
        rules.append(
            Rule(
                id=rule_id,
                why=why,
                kernels=_strings(table.get("kernels"), f"{where}.kernels", required=True),
                statuses=_strings(table.get("status"), f"{where}.status", required=True),
                expected=_strings(table.get("expected"), f"{where}.expected"),
                campaigns=_strings(table.get("campaigns"), f"{where}.campaigns"),
                labels=_strings(table.get("labels"), f"{where}.labels"),
                output=re.compile(output, re.MULTILINE) if output is not None else None,
                sites=_strings(table.get("sites"), f"{where}.sites"),
                reference=re.compile(reference, re.MULTILINE) if reference is not None else None,
            )
        )
    return tuple(rules)


def load_triage(extra: Sequence[Path] = ()) -> tuple[Rule, ...]:
    """Rules from ``extra`` files (tried first), then the built-in ones."""
    return tuple(rule for path in (*extra, BUILTIN_RULES) for rule in load_rules(path))


def expected_status(oracle: str | None, statuses: Mapping[str, str]) -> str:
    if oracle == "guaranteed-accept":
        return "accept"
    if oracle == "guaranteed-reject":
        return "reject"
    if statuses.get(REFERENCE_KERNEL) in {"accept", "reject"}:
        return statuses[REFERENCE_KERNEL]
    verdicts = Counter(status for status in statuses.values() if status in {"accept", "reject"})
    return verdicts.most_common(1)[0][0] if verdicts else "accept"


def triage(
    rules: tuple[Rule, ...],
    campaign: str,
    label: str,
    oracle: str | None,
    results: Mapping[str, Mapping[str, object]],
    sites: frozenset[str] = frozenset(),
) -> Triage:
    """Explain each kernel whose status deviates from the expected verdict."""
    statuses = {name: str(result.get("status")) for name, result in results.items()}
    expected = expected_status(oracle, statuses)
    reference = results.get(REFERENCE_KERNEL, {})
    case = Case(campaign, label, expected, sites, str(reference.get("output") or ""))
    explained: dict[str, str] = {}
    unexplained: list[str] = []
    for name, status in sorted(statuses.items()):
        if status == expected:
            continue
        output = str(results[name].get("output") or "")
        rule = next((rule for rule in rules if rule.explains(name, status, output, case)), None)
        if rule is None:
            unexplained.append(name)
        else:
            explained[name] = rule.id
    return Triage(expected, explained, tuple(unexplained))


def _references(line: dict[str, object]) -> Iterator[tuple[tuple[object, ...], str, str, int]]:
    """Yield ``(path, field, table, id)`` for every table reference in a line."""
    for sites, table in (
        (expression_reference_sites, "ie"),
        (name_reference_sites, "in"),
        (level_reference_sites, "il"),
    ):
        for path, field in sites(line):
            owner = _resolve(line, path)
            if owner is None or field not in owner:
                continue
            value = owner[field]
            if field in {"str", "num"} and isinstance(value, dict):
                value = value.get("pre")
            for item in value if isinstance(value, list) else [value]:
                if isinstance(item, int) and not isinstance(item, bool):
                    yield path, field, table, item


def _site(path: Sequence[object], field: str) -> str:
    return ".".join(str(part) for part in (*path, field) if not isinstance(part, int))


def mutation_sites(lines: Sequence[dict[str, object]], mutation: Mapping[str, object]) -> frozenset[str]:
    """Declaration fields a field-edit mutation lands in (see module doc)."""
    line_no, field = mutation.get("line"), mutation.get("field")
    path = mutation.get("path")
    path = tuple(path) if isinstance(path, list) else ()
    if not isinstance(field, str) or mutation.get("rewrite") is not None:
        return frozenset()
    if path and path[0] in DECLARATION_ROOTS:
        return frozenset({_site(path, field)})
    if not isinstance(line_no, int) or not 0 <= line_no < len(lines):
        return frozenset()
    owner = _resolve(lines[line_no], path)
    if owner is None or field not in owner:
        return frozenset()  # the stored document no longer matches the mutation
    target = declares_table_id(lines[line_no])
    if target is None:
        return frozenset({_site(path, field)})
    users: dict[tuple[str, int], list[tuple[int, tuple[object, ...], str]]] = defaultdict(list)
    for index, line in enumerate(lines):
        for ref_path, ref_field, table, identifier in _references(line):
            users[(table, identifier)].append((index, ref_path, ref_field))
    sites: set[str] = set()
    seen, pending = {target}, [target]
    while pending:
        for index, ref_path, ref_field in users.get(pending.pop(), ()):
            declared = declares_table_id(lines[index])
            if declared is None:
                sites.add(_site(ref_path, ref_field))
            elif declared not in seen:
                seen.add(declared)
                pending.append(declared)
    return frozenset(sites) or frozenset({"unreachable"})


def triage_metadata(
    rules: tuple[Rule, ...],
    metadata: Mapping[str, object],
    lines: Sequence[dict[str, object]] | None = None,
) -> Triage | None:
    """Triage a stored finding from its sidecar metadata (and document)."""
    mutation = metadata.get("mutation")
    results = metadata.get("results")
    if not isinstance(mutation, dict) or not isinstance(results, dict):
        return None
    stored = metadata.get("sites")
    if isinstance(stored, list):
        sites = frozenset(str(site) for site in stored)
    else:
        sites = mutation_sites(lines or (), mutation)
    return triage(
        rules,
        str(mutation.get("campaign") or ""),
        str(mutation.get("label") or ""),
        mutation.get("oracle") if isinstance(mutation.get("oracle"), str) else None,
        {name: value for name, value in results.items() if isinstance(value, dict)},
        sites,
    )
