"""Mutation score: does Pestycyd catch defects seeded into a checker?

A discovery benchmark replays bugs somebody already found.  Seeded
defects measure the search on bugs nobody has looked for: a mutant
checker is a real checker with one check removed or weakened (see
``tools/mutants``), and a mutant is *killed* when some input makes it
disagree with the reference kernel while the unmodified build — the
pristine control — still agrees.  The control is what separates the
seeded defect from divergences the checker already had.

Each mutant is tried twice: first against the seeds alone, which says
what the corpus already catches, then through a budgeted hunt, which
says what mutation adds on top.
"""

from __future__ import annotations

import dataclasses
import json
import shutil
import tomllib
from dataclasses import dataclass
from pathlib import Path

from .config import Config, KernelSpec
from .ndjson import files
from .runner import run_matrix
from .store import atomic_text

PRISTINE = "pristine"
MUTANT = "mutant"


@dataclass(frozen=True)
class Plan:
    reference: str
    like: str
    manifest: Path
    paths: tuple[str, ...]
    campaigns: tuple[str, ...] | None
    skip_campaigns: tuple[str, ...]
    iterations: int
    budget_seconds: float | None
    seed: int
    max_depth: int
    max_children: int


def load_plan(path: Path) -> Plan:
    path = path.resolve()
    raw = tomllib.loads(path.read_text())
    if raw.get("version") != 1:
        raise ValueError("efficacy plan needs version = 1")
    for key in ("reference", "like", "manifest"):
        if not isinstance(raw.get(key), str):
            raise ValueError(f"efficacy plan needs a string {key!r}")
    paths = raw.get("paths")
    if not isinstance(paths, list) or not paths or not all(isinstance(item, str) for item in paths):
        raise ValueError("efficacy plan needs a non-empty string array 'paths'")
    campaigns = raw.get("campaigns")
    if campaigns is not None and (
        not isinstance(campaigns, list) or not all(isinstance(item, str) for item in campaigns)
    ):
        raise ValueError("efficacy plan 'campaigns' must be a string array")
    skip = raw.get("skip_campaigns", [])
    if not isinstance(skip, list) or not all(isinstance(item, str) for item in skip):
        raise ValueError("efficacy plan 'skip_campaigns' must be a string array")
    budget = raw.get("budget_seconds")
    if budget is not None and not isinstance(budget, (int, float)):
        raise ValueError("efficacy plan 'budget_seconds' must be a number")
    base = path.parent
    return Plan(
        reference=raw["reference"],
        like=raw["like"],
        manifest=(base / raw["manifest"]).resolve(),
        paths=tuple(str((base / item).resolve()) for item in paths),
        campaigns=tuple(campaigns) if campaigns else None,
        skip_campaigns=tuple(skip),
        iterations=int(raw.get("iterations", 300)),
        budget_seconds=None if budget is None else float(budget),
        seed=int(raw.get("seed_rnd", 0)),
        max_depth=int(raw.get("max_depth", 3)),
        max_children=int(raw.get("max_children", 256)),
    )


def variant(base: KernelSpec, binary_name: str, binary: str, name: str) -> KernelSpec:
    """``base`` with its checker binary swapped for a seeded-defect build.

    The checker is the command argument whose file name is the manifest's
    ``binary_name``, so a plan does not depend on where it was built.
    """
    matches = [part for part in base.command if Path(part).name == binary_name]
    if len(matches) != 1:
        raise ValueError(
            f"kernel {base.name!r} command needs exactly one {binary_name!r} argument, found {len(matches)}"
        )
    command = tuple(binary if part == matches[0] else part for part in base.command)
    return dataclasses.replace(base, name=name, command=command, probe=None, feedback=None)


def kills(reference: str, statuses: dict[str, str]) -> bool:
    expected = statuses[reference]
    return statuses[PRISTINE] == expected and statuses[MUTANT] != expected


def run_efficacy(config: Config, args) -> int:
    from .campaigns import selected as selected_campaigns
    from .cli import HuntParams, run_hunt

    plan = load_plan(args.plan)
    # Campaigns that only exercise a checker's known by-design divergences
    # spend the budget without any chance of a kill.
    campaigns = [
        campaign.name
        for campaign in selected_campaigns(list(plan.campaigns) if plan.campaigns else None)
        if campaign.name not in plan.skip_campaigns
    ]
    (reference,) = config.selected([plan.reference])
    (base,) = config.selected([plan.like])
    manifest = json.loads(plan.manifest.read_text())
    mutants = manifest["mutants"]
    if args.filter:
        missing = set(args.filter).difference(mutant["name"] for mutant in mutants)
        if missing:
            raise ValueError(f"unknown mutants: {', '.join(sorted(missing))}")
        mutants = [mutant for mutant in mutants if mutant["name"] in args.filter]
    pristine = variant(base, manifest["binary_name"], manifest["pristine"], PRISTINE)
    seeds = files(list(plan.paths))
    state_root = (args.state or config.state) / "efficacy"

    rows: list[dict[str, object]] = []
    for mutant in mutants:
        kernels = (reference, pristine, variant(base, manifest["binary_name"], mutant["binary"], MUTANT))
        row: dict[str, object] = {
            "name": mutant["name"],
            "description": mutant["description"],
            "history": mutant.get("history"),
            "killed_by": None,
        }
        for seed in seeds:
            statuses = {name: outcome.status for name, outcome in run_matrix(kernels, seed).items()}
            if kills(reference.name, statuses):
                row["killed_by"] = "seed"
                row["evidence"] = {"file": str(seed), "statuses": statuses}
                break
        if row["killed_by"] is None:
            state = state_root / mutant["name"]
            if state.exists():
                shutil.rmtree(state)
            summary = run_hunt(
                config,
                kernels,
                HuntParams(
                    paths=list(plan.paths),
                    campaigns=campaigns,
                    iterations=plan.iterations,
                    seed=plan.seed,
                    seed_policy="accepted",
                    max_depth=plan.max_depth,
                    max_children=plan.max_children,
                    semantic_only=True,
                    budget_seconds=plan.budget_seconds,
                    stop_on=lambda statuses: kills(reference.name, statuses),
                ),
                state,
            )
            row["attempts"] = summary.attempts
            row["no_seeds"] = summary.no_seeds or None
            row["seconds"] = round(summary.seconds, 3)
            hit = next((hit for hit in summary.findings if kills(reference.name, hit.statuses)), None)
            if hit is not None:
                row["killed_by"] = "hunt"
                row["evidence"] = {
                    "attempt": hit.attempt,
                    "label": hit.label,
                    "digest": hit.digest,
                    "statuses": hit.statuses,
                }
        rows.append(row)
        evidence = row.get("evidence") or {}
        if row["killed_by"] == "seed":
            note = f"killed by seed {Path(evidence['file']).name}"
        elif row["killed_by"] == "hunt":
            note = f"killed by hunt at attempt {evidence['attempt']} ({evidence['label']})"
        elif row["no_seeds"]:
            note = "SURVIVED untested: no seed every kernel accepts"
        else:
            note = f"SURVIVED {row['attempts']} attempts in {row['seconds']:.0f}s"
        statuses = evidence.get("statuses")
        vector = "" if not statuses else " [" + ", ".join(f"{k}={v}" for k, v in statuses.items()) + "]"
        print(f"efficacy {mutant['name']}: {note}{vector}", flush=True)

    killed = [row for row in rows if row["killed_by"]]
    by_seed = sum(1 for row in killed if row["killed_by"] == "seed")
    print(
        f"efficacy: {len(killed)}/{len(rows)} mutants killed "
        f"({by_seed} by seeds alone, {len(killed) - by_seed} only by hunting)"
    )
    if args.report:
        atomic_text(
            args.report,
            json.dumps(
                {
                    "schema": "pestycyd-efficacy-1",
                    "plan": str(args.plan),
                    "manifest": str(plan.manifest),
                    "reference": reference.name,
                    "killed": len(killed),
                    "total": len(rows),
                    "mutants": rows,
                },
                indent=2,
                ensure_ascii=False,
            )
            + "\n",
        )
    return 0
