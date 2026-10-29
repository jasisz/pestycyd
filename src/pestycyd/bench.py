"""Discovery benchmark: can this Pestycyd build actually find known bugs?

A scenario pins a historical defect family without handing the tool the
reproduction: a correct seed, a campaign selection, a fixed budget, and
the outcome vector that identifies the class of bug.  The benchmark then
reports whether the hunt reached it, after how many attempts, and how
many distinct canonical cases it produced.

Pinning checkers is deliberately outside the file: kernel versions come
from the active ``pestycyd.toml``, so the same scenarios measure both a
suspect checker build and its repaired successor.
"""

from __future__ import annotations

import json
import shutil
import tomllib
from dataclasses import dataclass
from pathlib import Path

from .config import Config
from .store import atomic_text

VALID_ESCALATIONS = {"forall-prop-prop"}
SEED_POLICIES = {"accepted", "consensus", "any", "all"}


@dataclass(frozen=True)
class Scenario:
    name: str
    description: str
    kernels: tuple[str, ...]
    paths: tuple[str, ...]
    campaigns: tuple[str, ...] | None
    iterations: int
    seed: int
    max_depth: int
    max_children: int
    seed_policy: str
    semantic_only: bool
    behavior_feedback: bool
    protect_final_goal: bool
    finding_expect: dict[str, str]
    finding_require_seed_change: bool
    budget_seconds: float | None
    escalation: str | None

    @property
    def oracle_driven(self) -> bool:
        """True when findings come from the mutation oracle, not a pinned vector.

        Guaranteed-accept and guaranteed-reject scenarios want this: the
        interesting event is defined by the oracle itself, so pinning an
        outcome vector would record healthy behavior as a finding.
        """
        return not self.finding_expect


def _string_list(table: dict[str, object], key: str, where: str) -> tuple[str, ...]:
    value = table.get(key)
    if value is None:
        return ()
    if not isinstance(value, list) or not all(isinstance(item, str) for item in value):
        raise ValueError(f"{where}.{key} must be a string array")
    return tuple(value)


def _require(table: dict[str, object], key: str, where: str) -> object:
    if key not in table:
        raise ValueError(f"{where} needs a {key!r} entry")
    return table[key]


def load_scenarios(path: Path) -> dict[str, Scenario]:
    path = path.resolve()
    with path.open("rb") as stream:
        raw = tomllib.load(stream)
    if raw.get("version") != 1:
        raise ValueError("scenario file needs version = 1")
    tables = raw.get("scenario")
    if not isinstance(tables, dict) or not tables:
        raise ValueError("scenario file needs at least one [scenario.NAME] table")

    from .cli import parse_expect

    base = path.parent
    scenarios: dict[str, Scenario] = {}
    for name, table in tables.items():
        if not isinstance(table, dict):
            raise ValueError(f"scenario.{name} must be a table")
        where = f"scenario.{name}"
        kernels = _string_list(table, "kernels", where)
        if not kernels:
            raise ValueError(f"{where}.kernels must name at least one kernel")
        raw_paths = _string_list(table, "paths", where)
        seed_value = table.get("seed")
        if isinstance(seed_value, str):
            raw_paths = (seed_value, *raw_paths)
        if not raw_paths:
            raise ValueError(f"{where} needs seed or paths")
        finding_rows = _string_list(table, "finding", where)
        finding_expect: dict[str, str] = {}
        for row in finding_rows:
            kernel_name, status = parse_expect(row)
            finding_expect[kernel_name] = status
        unknown = set(finding_expect).difference(kernels)
        if unknown:
            raise ValueError(
                f"{where}.finding names kernels outside {where}.kernels: "
                f"{', '.join(sorted(unknown))}"
            )
        campaigns = _string_list(table, "campaigns", where) or None
        iterations = table.get("iterations", 500)
        if not isinstance(iterations, int) or isinstance(iterations, bool) or iterations < 1:
            raise ValueError(f"{where}.iterations must be a positive integer")
        seed = table.get("seed_rnd", 0)
        if not isinstance(seed, int) or isinstance(seed, bool):
            raise ValueError(f"{where}.seed_rnd must be an integer")
        max_depth = table.get("max_depth", 3)
        max_children = table.get("max_children", 256)
        seed_policy = table.get("seed_policy", "accepted")
        if seed_policy not in SEED_POLICIES:
            raise ValueError(f"{where}.seed_policy is unknown")
        escalation = table.get("escalation")
        if escalation is not None and escalation not in VALID_ESCALATIONS:
            raise ValueError(f"{where}.escalation must be one of {sorted(VALID_ESCALATIONS)}")
        budget = table.get("budget_seconds")
        if budget is not None and (not isinstance(budget, (int, float)) or budget <= 0):
            raise ValueError(f"{where}.budget_seconds must be positive")
        paths: list[str] = []
        for item in raw_paths:
            resolved = (base / item).resolve()
            if not resolved.exists():
                raise ValueError(f"{where} input does not exist: {item}")
            paths.append(str(resolved))
        scenarios[name] = Scenario(
            name=name,
            description=str(table.get("description", "")),
            kernels=kernels,
            paths=tuple(paths),
            campaigns=campaigns,
            iterations=iterations,
            seed=seed,
            max_depth=max_depth,
            max_children=max_children,
            seed_policy=str(seed_policy),
            semantic_only=bool(table.get("semantic_only", True)),
            behavior_feedback=bool(table.get("behavior_feedback", False)),
            protect_final_goal=bool(table.get("protect_final_goal", False)),
            finding_expect=finding_expect,
            finding_require_seed_change=bool(table.get("require_seed_change", False)),
            budget_seconds=None if budget is None else float(budget),
            escalation=str(escalation) if escalation is not None else None,
        )
    return scenarios


def run_bench(config: Config, args) -> int:
    from .cli import HuntParams, run_hunt

    scenarios = load_scenarios(args.scenarios)
    if args.filter:
        missing = set(args.filter).difference(scenarios)
        if missing:
            raise ValueError(f"unknown scenarios: {', '.join(sorted(missing))}")
        scenarios = {
            name: scenario for name, scenario in scenarios.items() if name in set(args.filter)
        }

    state_root = args.state or config.state
    report: dict[str, object] = {
        "schema": "pestycyd-bench-1",
        "scenarios_file": str(args.scenarios),
        "scenarios": [],
    }
    for name, scenario in scenarios.items():
        kernels = config.selected(list(scenario.kernels))
        by_name = {kernel.name: kernel for kernel in kernels}
        ordered = tuple(by_name[kernel] for kernel in scenario.kernels)
        scenario_state = state_root / "bench" / name
        if scenario_state.exists():
            shutil.rmtree(scenario_state)
        params = HuntParams(
            paths=list(scenario.paths),
            campaigns=list(scenario.campaigns) if scenario.campaigns else None,
            iterations=scenario.iterations,
            seed=scenario.seed,
            seed_policy=scenario.seed_policy,
            max_depth=scenario.max_depth,
            max_children=scenario.max_children,
            semantic_only=scenario.semantic_only,
            behavior_feedback=scenario.behavior_feedback,
            protect_final_goal=scenario.protect_final_goal,
            finding_expect=dict(scenario.finding_expect),
            finding_require_seed_change=scenario.finding_require_seed_change,
            budget_seconds=scenario.budget_seconds,
        )

        def notify(message: str, _name: str = name) -> None:
            print(f"[{_name}] {message}")

        summary = run_hunt(config, ordered, params, scenario_state, notify)
        clusters: dict[str, list[object]] = {}
        for hit in summary.findings:
            key = hit.canonical_digest or f"raw:{hit.digest}"
            clusters.setdefault(key, []).append(hit)
        canonical_false_any = any(hit.canonical_false for hit in summary.findings)
        escalation_reached = (
            scenario.escalation == "forall-prop-prop" and canonical_false_any
        )
        first = summary.findings[0] if summary.findings else None
        row: dict[str, object] = {
            "name": name,
            "description": scenario.description,
            "kernels": scenario.kernels,
            "paths": scenario.paths,
            "campaigns": scenario.campaigns,
            "iterations": scenario.iterations,
            "budget_seconds": scenario.budget_seconds,
            "found": bool(summary.findings),
            "attempts": summary.attempts,
            "seconds": round(summary.seconds, 3),
            "budget_exhausted": summary.budget_exhausted,
            "first_finding": None
            if first is None
            else {
                "attempt": first.attempt,
                "digest": first.digest,
                "canonical_digest": first.canonical_digest,
                "label": first.label,
                "statuses": first.statuses,
            },
            "novel_findings": summary.novel_findings,
            "clusters": [
                {
                    "canonical_digest": key,
                    "findings": len(hits),
                    "canonical_false": any(hit.canonical_false for hit in hits),
                    "statuses": hits[0].statuses,
                }
                for key, hits in sorted(clusters.items())
            ],
            "escalation_reached": escalation_reached or None,
            "canonical_false_any": canonical_false_any or None,
            "coverage_inputs": summary.coverage_inputs,
            "feedback_features": summary.feedback_features,
        }
        report["scenarios"].append(row)
        verdict = "FOUND" if summary.findings else "miss"
        first_note = (
            "" if first is None else f", first at attempt {first.attempt} ({first.label})"
        )
        escalation_note = " [∀P:Prop,P closed]" if escalation_reached else ""
        print(
            f"bench {name}: {verdict} — {summary.attempts} attempts in "
            f"{summary.seconds:.1f}s, {len(clusters)} cluster(s), "
            f"{summary.novel_findings} novel{first_note}{escalation_note}"
        )

    if args.report:
        atomic_text(
            args.report, json.dumps(report, indent=2, ensure_ascii=False) + "\n"
        )
        print(f"bench report: {args.report}")
    found = sum(1 for row in report["scenarios"] if row["found"])
    print(
        f"bench: {found}/{len(report['scenarios'])} scenario(s) reproduced their "
        "target outcome vector"
    )
    return 0
