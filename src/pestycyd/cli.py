from __future__ import annotations

import argparse
import dataclasses
import hashlib
import json
import random
import sys
import tempfile
import time
import tomllib
from collections import deque
from pathlib import Path
from typing import Callable

from .bench import run_bench
from .campaigns import CAMPAIGNS, selected as selected_campaigns
from .config import Config, KernelSpec, load_config
from .generators import app_spine, con_k_params, deep_binder
from .minimize import ddmin, well_formed_export
from .ndjson import Document, Mutation, files
from .outcomes import Outcome
from .rewrite import canonical_false_theorem, canonicalize
from .runner import run_matrix, run_probe
from .store import FindingStore, atomic_text


def matrix_json(results: dict[str, Outcome]) -> dict[str, object]:
    return {name: outcome.json() for name, outcome in results.items()}


def statuses(results: dict[str, Outcome]) -> str:
    return ", ".join(f"{name}={result.status}" for name, result in results.items())


def is_interesting(
    mutation: Mutation,
    results: dict[str, Outcome],
    include_robustness: bool = True,
    tolerated: dict[str, frozenset[str]] | None = None,
) -> tuple[bool, str]:
    ignored = tolerated or {}

    def severe(name: str, status: str) -> bool:
        return (
            status in {"crash", "timeout", "error", "runner-error"}
            and status not in ignored.get(name, ())
        )

    values = [outcome.status for outcome in results.values()]
    if mutation.oracle == "guaranteed-reject":
        accepted = [name for name, outcome in results.items() if outcome.status == "accept"]
        if accepted:
            return True, "accepted guaranteed-invalid input"
        robustness = include_robustness and any(
            severe(name, outcome.status) for name, outcome in results.items()
        )
        return robustness, "kernel robustness failure"
    if mutation.oracle == "guaranteed-accept":
        failures = [
            name
            for name, outcome in results.items()
            if outcome.status != "accept"
            and (include_robustness or outcome.status in {"reject", "decline"})
            and outcome.status not in ignored.get(name, ())
        ]
        return bool(failures), "failed validity-preserving input"
    semantic = [value for value in values if value in {"accept", "reject", "decline"}]
    different = len(set(semantic)) > 1
    robustness = include_robustness and any(
        severe(name, outcome.status) for name, outcome in results.items()
    )
    return robustness or different, "kernel robustness failure" if robustness else "differential outcome"


def feedback_features(
    results: dict[str, Outcome], *, include_behavior: bool = False,
) -> set[str]:
    features = {
        f"{name}:{feature}"
        for name, outcome in results.items()
        for feature in outcome.feedback
    }
    if include_behavior:
        features.update(
            f"{name}:behavior:{outcome.status}:{outcome.fingerprint}"
            for name, outcome in results.items()
        )
    return features


def seed_is_eligible(policy: str, results: dict[str, Outcome]) -> bool:
    values = [outcome.status for outcome in results.values()]
    if policy == "accepted":
        return all(value == "accept" for value in values)
    severe = {"timeout", "crash", "error", "runner-error"}
    if policy == "consensus":
        return len(set(values)) == 1 and values[0] in {"accept", "reject"}
    if policy == "any":
        return not severe.intersection(values)
    if policy == "all":
        return True
    raise ValueError(f"unknown seed policy: {policy}")


def matches_expectations(
    expected: dict[str, str], results: dict[str, Outcome]
) -> bool:
    return all(
        name in results and results[name].status == status
        for name, status in expected.items()
    )


def doctor(config: Config, kernels: tuple[KernelSpec, ...], _args: argparse.Namespace) -> int:
    failures = 0
    for kernel in kernels:
        ok, message = run_probe(kernel)
        print(f"{'ok' if ok else 'FAIL'} {kernel.name}: {message}")
        failures += not ok
    return 1 if failures else 0


def list_campaigns(_config: Config, _kernels: tuple[KernelSpec, ...], _args: argparse.Namespace) -> int:
    for campaign in CAMPAIGNS.values():
        print(f"{campaign.name} [{campaign.oracle}]\n  {campaign.description}")
        print(f"  targets: {', '.join(campaign.targets)}")
    return 0


def generate_deep_binder(
    _config: Config | None, _kernels: tuple[KernelSpec, ...], args: argparse.Namespace
) -> int:
    atomic_text(args.output, deep_binder(args.depth))
    print(f"generated deep-binder depth {args.depth}: {args.output}")
    return 0


def generate_con_k(
    _config: Config | None, _kernels: tuple[KernelSpec, ...], args: argparse.Namespace
) -> int:
    atomic_text(args.output, con_k_params(args.count))
    print(f"generated con-k-params width {args.count}: {args.output}")
    return 0


def generate_app_spine(
    _config: Config | None, _kernels: tuple[KernelSpec, ...], args: argparse.Namespace
) -> int:
    atomic_text(args.output, app_spine(args.depth))
    print(f"generated app-spine depth {args.depth}: {args.output}")
    return 0


def matrix_command(config: Config, kernels: tuple[KernelSpec, ...], args: argparse.Namespace) -> int:
    paths = files(args.paths)
    rows: list[dict[str, object]] = []
    differences = 0
    for path in paths:
        results = run_matrix(kernels, path, args.workers)
        row = {"file": str(path), "results": matrix_json(results)}
        rows.append(row)
        values = {result.status for result in results.values()}
        if len(values) > 1 or any(
            value in {"crash", "timeout", "error", "runner-error"} for value in values
        ):
            differences += 1
            print(f"DIFFER {path}: {statuses(results)}")
        elif args.verbose:
            print(f"{path}: {statuses(results)}")
    report = {"schema": "pestycyd-matrix-1", "kernels": [k.public() for k in kernels], "runs": rows}
    if args.report:
        atomic_text(args.report, json.dumps(report, indent=2, ensure_ascii=False) + "\n")
    print(f"matrix: {len(paths)} inputs, {len(kernels)} kernels, {differences} interesting")
    return 1 if differences else 0


@dataclasses.dataclass
class HuntParams:
    paths: list[str]
    campaigns: list[str] | None
    iterations: int | None
    seed: int
    seed_policy: str
    max_depth: int
    max_children: int
    semantic_only: bool = False
    behavior_feedback: bool = False
    feedback_depth_first: bool = False
    protect_final_goal: bool = False
    finding_expect: dict[str, str] = dataclasses.field(default_factory=dict)
    finding_require_seed_change: bool = False
    budget_seconds: float | None = None
    workers: int | None = None
    verbose: bool = False


@dataclasses.dataclass
class FindingHit:
    attempt: int
    digest: str
    novel: bool
    label: str
    statuses: dict[str, str]
    canonical_digest: str | None
    canonical_false: bool


@dataclasses.dataclass
class HuntSummary:
    attempts: int
    seconds: float
    findings: list[FindingHit]
    coverage_inputs: int
    feedback_features: int
    budget_exhausted: bool
    no_seeds: bool = False

    @property
    def novel_findings(self) -> int:
        return sum(1 for finding in self.findings if finding.novel)


def _compose_lineage_oracle(parent_oracle: str, mutation_oracle: str) -> str:
    """Oracle of a child document, given the parent's and the mutation's.

    A chain of validity-preserving transforms is itself validity
    preserving, so ``guaranteed-accept`` survives composition with
    another ``guaranteed-accept`` step; anything else is differential.
    """
    if (
        parent_oracle == "guaranteed-accept"
        and mutation_oracle == "guaranteed-accept"
    ):
        return "guaranteed-accept"
    return "differential"


def run_hunt(
    config: Config,
    kernels: tuple[KernelSpec, ...],
    params: HuntParams,
    state_root: Path,
    notify: Callable[[str], None] | None = None,
) -> HuntSummary:
    def say(message: str) -> None:
        if notify is not None:
            notify(message)

    paths = files(params.paths)
    campaigns = selected_campaigns(params.campaigns)
    finding_expect = dict(params.finding_expect)
    unknown = set(finding_expect).difference(kernel.name for kernel in kernels)
    if unknown:
        raise ValueError(
            f"finding expectations name unknown kernels: {', '.join(sorted(unknown))}"
        )
    started = time.perf_counter()
    rng = random.Random(params.seed)
    store = FindingStore(state_root)
    # Fingerprinting a checker can mean hashing a large native executable.  A hunt
    # records the same checker snapshot for every candidate, so compute it once
    # instead of re-reading every executable on every mutation.
    kernel_metadata = [kernel.public() for kernel in kernels]
    frontier: list[
        tuple[
            Path,
            Document,
            Mutation,
            int,
            tuple[dict[str, object], ...],
            frozenset[int],
            bool,
            str,
        ]
    ] = []
    frontier_buckets: list[
        list[
            tuple[
                Path,
                Document,
                Mutation,
                int,
                tuple[dict[str, object], ...],
                frozenset[int],
                bool,
                str,
            ]
        ]
    ] = []
    seen_feedback: set[str] = set()
    seen_inputs: set[str] = set()

    def allowed(mutation: Mutation, protected: frozenset[int]) -> bool:
        return (
            mutation.line not in protected
            and all(edit.line not in protected for edit in mutation.edits)
            and all(
                edit.kind == "insert" or edit.line not in protected
                for edit in mutation.line_edits
            )
        )

    for path in paths:
        try:
            document = Document.load(path)
        except (OSError, ValueError, json.JSONDecodeError) as failure:
            say(f"SKIP {path}: {failure}")
            continue
        seen_inputs.add(hashlib.sha256(document.render().encode()).hexdigest())
        baseline = run_matrix(kernels, path, params.workers)
        if not seed_is_eligible(params.seed_policy, baseline):
            say(
                f"SKIP {path}: seed does not satisfy {params.seed_policy} policy; "
                f"{statuses(baseline)}"
            )
            continue
        seen_feedback.update(
            feedback_features(baseline, include_behavior=params.behavior_feedback)
        )
        protected = (
            document.final_goal_lines() if params.protect_final_goal else frozenset()
        )
        seed_matches_finding = bool(finding_expect) and matches_expectations(
            finding_expect, baseline
        )
        mutations = [
            mutation
            for campaign in campaigns
            for mutation in campaign.generate(document)
            if allowed(mutation, protected)
        ]
        bucket = [
            (path, document, mutation, 1, (), protected, seed_matches_finding, "")
            for mutation in mutations
        ]
        rng.shuffle(bucket)
        frontier_buckets.append(bucket)
    while any(frontier_buckets):
        for bucket in frontier_buckets:
            if bucket:
                frontier.append(bucket.pop())
    if not frontier:
        say("no accepted seed has mutations for the selected campaigns")
        return HuntSummary(
            0, time.perf_counter() - started, [], 0, len(seen_feedback), False, no_seeds=True
        )
    queue = deque(frontier)
    tolerated_statuses = {
        kernel.name: frozenset(kernel.tolerate) for kernel in kernels if kernel.tolerate
    }
    hits: list[FindingHit] = []
    findings = 0
    novel = 0
    corpus = 0
    attempts = 0
    budget_exhausted = False
    # A validity-preserving transform proves the child correct only when
    # the parent was correct.  Seed policies other than "accepted" admit
    # inputs some kernel already rejects, so the guaranteed-accept oracle
    # would flag pre-existing rejections as completeness findings.
    sound_accept_oracle = params.seed_policy == "accepted"
    with tempfile.TemporaryDirectory(prefix="pestycyd-hunt-") as directory:
        candidate = Path(directory) / "candidate.ndjson"
        while queue and (params.iterations is None or attempts < params.iterations):
            if (
                params.budget_seconds is not None
                and time.perf_counter() - started > params.budget_seconds
            ):
                budget_exhausted = True
                break
            (
                seed,
                document,
                original,
                depth,
                lineage,
                protected,
                seed_matches_finding,
                parent_oracle,
            ) = queue.popleft()
            if depth == 1:
                oracle = original.oracle
                if oracle == "guaranteed-accept" and not sound_accept_oracle:
                    oracle = "differential"
            else:
                oracle = _compose_lineage_oracle(parent_oracle, original.oracle)
            mutation = original if oracle == original.oracle else dataclasses.replace(original, oracle=oracle)
            child = document.mutated(mutation)
            child_protected = (
                child.final_goal_lines() if params.protect_final_goal else frozenset()
            )
            content = child.render()
            content_digest = hashlib.sha256(content.encode()).hexdigest()
            if content_digest in seen_inputs:
                continue
            seen_inputs.add(content_digest)
            attempts += 1
            candidate.write_text(content)
            results = run_matrix(kernels, candidate, params.workers)
            interesting, reason = is_interesting(
                mutation,
                results,
                include_robustness=not params.semantic_only,
                tolerated=tolerated_statuses,
            )
            if finding_expect:
                candidate_matches = matches_expectations(finding_expect, results)
                inherited = params.finding_require_seed_change and seed_matches_finding
                interesting = candidate_matches and not inherited
                if inherited and candidate_matches:
                    reason = "seed already matched requested finding outcomes"
                elif candidate_matches:
                    reason = "matched requested finding outcomes"
                else:
                    reason = "did not match requested finding outcomes"
            features = feedback_features(
                results, include_behavior=params.behavior_feedback
            )
            added = features.difference(seen_feedback)
            seen_feedback.update(features)
            history = (*lineage, mutation.json())
            metadata: dict[str, object] = {
                "seed": str(seed),
                "mutation": mutation.json(),
                "lineage": list(history),
                "depth": depth,
                "protected_goal_lines": sorted(line + 1 for line in child_protected),
                "seed_matched_finding_expectations": seed_matches_finding,
                "reason": reason,
                "feedback": {
                    "new": len(added),
                    "new_features": sorted(added)[:256],
                    "new_features_truncated": len(added) > 256,
                    "total_seen": len(seen_feedback),
                },
                "kernels": kernel_metadata,
                "results": matrix_json(results),
            }
            if interesting:
                findings += 1
                digest, created = store.save(content, metadata)
                novel += created
                canonical = canonicalize(child)
                canonical_digest = (
                    hashlib.sha256(canonical.render().encode()).hexdigest()
                    if canonical is not None
                    else None
                )
                hits.append(
                    FindingHit(
                        attempt=attempts,
                        digest=digest,
                        novel=created,
                        label=mutation.label,
                        statuses={
                            name: outcome.status for name, outcome in results.items()
                        },
                        canonical_digest=canonical_digest,
                        canonical_false=(
                            canonical_false_theorem(canonical)
                            if canonical is not None
                            else canonical_false_theorem(child)
                        ),
                    )
                )
                say(
                    f"{'FINDING' if created else 'KNOWN'} {digest[:12]} {mutation.label}: "
                    f"{statuses(results)}"
                )
            if added:
                coverage_metadata = dict(metadata)
                coverage_metadata["reason"] = "novel search feedback"
                digest, created = store.save_corpus(content, coverage_metadata)
                corpus += created
                if not interesting:
                    say(
                        f"COVERAGE {digest[:12]} +{len(added)} {mutation.label}: "
                        f"{statuses(results)}"
                    )
                if depth < params.max_depth:
                    descendants = [
                        next_mutation
                        for campaign in campaigns
                        for next_mutation in campaign.generate(child)
                        if allowed(next_mutation, child_protected)
                    ]
                    rng.shuffle(descendants)
                    descendants = descendants[: params.max_children]
                    entries = [
                        (
                            seed,
                            child,
                            next_mutation,
                            depth + 1,
                            history,
                            child_protected,
                            seed_matches_finding,
                            oracle,
                        )
                        for next_mutation in descendants
                    ]
                    if params.feedback_depth_first:
                        queue.extendleft(reversed(entries))
                    else:
                        queue.extend(entries)
            elif params.verbose:
                say(f"ok {attempts} {mutation.label}: {statuses(results)}")
    return HuntSummary(
        attempts=attempts,
        seconds=time.perf_counter() - started,
        findings=hits,
        coverage_inputs=corpus,
        feedback_features=len(seen_feedback),
        budget_exhausted=budget_exhausted,
    )


def hunt(config: Config, kernels: tuple[KernelSpec, ...], args: argparse.Namespace) -> int:
    params = HuntParams(
        paths=args.paths,
        campaigns=args.campaign,
        iterations=args.iterations,
        seed=args.seed,
        seed_policy=args.seed_policy,
        max_depth=args.max_depth,
        max_children=args.max_children,
        semantic_only=args.semantic_only,
        behavior_feedback=getattr(args, "behavior_feedback", False),
        feedback_depth_first=getattr(args, "feedback_depth_first", False),
        protect_final_goal=getattr(args, "protect_final_goal", False),
        finding_expect=dict(getattr(args, "finding_expect", ())),
        finding_require_seed_change=getattr(args, "finding_require_seed_change", False),
        budget_seconds=getattr(args, "budget_seconds", None),
        workers=getattr(args, "workers", None),
        verbose=args.verbose,
    )
    summary = run_hunt(config, kernels, params, args.state or config.state, print)
    print(
        f"hunt: {summary.attempts} mutations, {len(summary.findings)} interesting, "
        f"{summary.novel_findings} novel findings, {summary.coverage_inputs} coverage inputs, "
        f"{summary.feedback_features} feedback features"
    )
    if summary.no_seeds:
        return 2
    return 1 if summary.findings else 0


def parse_expect(value: str) -> tuple[str, str]:
    if "=" not in value:
        raise argparse.ArgumentTypeError("expectation must be KERNEL=STATUS")
    name, status = value.split("=", 1)
    allowed = {"accept", "reject", "decline", "timeout", "crash", "error", "runner-error"}
    if not name or status not in allowed:
        raise argparse.ArgumentTypeError("invalid KERNEL=STATUS expectation")
    return name, status


def minimize_command(config: Config, kernels: tuple[KernelSpec, ...], args: argparse.Namespace) -> int:
    expected = dict(args.expect)
    unknown = set(expected).difference(kernel.name for kernel in kernels)
    if unknown:
        raise ValueError(f"expectations name unknown kernels: {', '.join(sorted(unknown))}")
    lines = args.input.read_text().splitlines()
    tests = 0
    with tempfile.TemporaryDirectory(prefix="pestycyd-minimize-") as directory:
        candidate = Path(directory) / "candidate.ndjson"

        def interesting(trial: list[str]) -> bool:
            nonlocal tests
            tests += 1
            if not args.allow_malformed and not well_formed_export(trial):
                return False
            candidate.write_text("\n".join(trial) + "\n")
            results = run_matrix(kernels, candidate, args.workers)
            return all(results[name].status == status for name, status in expected.items())

        if not interesting(lines):
            print("input does not satisfy the requested outcomes", file=sys.stderr)
            return 2
        reduced = ddmin(lines, interesting, tuple(args.keep))
    atomic_text(args.output, "\n".join(reduced) + "\n")
    print(f"minimized {len(lines)} -> {len(reduced)} lines in {tests} tests: {args.output}")
    return 0


def reduce_command(config: Config, kernels: tuple[KernelSpec, ...], args: argparse.Namespace) -> int:
    """Delete records while preserving outcomes, renumbering tables on every trial.

    Unlike ``minimize``, the predicate canonicalizes each trial first:
    unreachable records are garbage-collected and the name, level, and
    expression tables are renumbered densely, so deleting a record from
    the middle of a table no longer collapses the case into a parser
    failure.  Inputs that rely on duplicate table identifiers (for
    example intern-table shadowing findings) fall back to plain line
    minimization, because renumbering would erase the defect itself.
    """
    expected = dict(args.expect)
    unknown = set(expected).difference(kernel.name for kernel in kernels)
    if unknown:
        raise ValueError(f"expectations name unknown kernels: {', '.join(sorted(unknown))}")
    lines = args.input.read_text().splitlines()
    parsed: list[dict[str, object]] = []
    for line in lines:
        if line.strip():
            value = json.loads(line)
            if not isinstance(value, dict):
                raise ValueError(f"{args.input}: line is not a JSON object")
            parsed.append(value)
    graph_mode = canonicalize(Document(tuple(parsed))) is not None
    if not graph_mode:
        print(
            "reduce: duplicate table identifiers; falling back to line minimization"
        )
    tests = 0
    with tempfile.TemporaryDirectory(prefix="pestycyd-reduce-") as directory:
        candidate = Path(directory) / "candidate.ndjson"

        def interesting(trial: list[str]) -> bool:
            nonlocal tests
            tests += 1
            rows: list[dict[str, object]] = []
            for line in trial:
                if not line.strip():
                    continue
                try:
                    value = json.loads(line)
                except (TypeError, ValueError, json.JSONDecodeError):
                    return False
                if not isinstance(value, dict):
                    return False
                rows.append(value)
            if not rows:
                return False
            document = Document(tuple(rows))
            if graph_mode:
                canonical = canonicalize(document)
                if canonical is None:
                    return False
            else:
                if not args.allow_malformed and not well_formed_export(trial):
                    return False
                canonical = document
            text = canonical.render()
            if not args.allow_malformed and not well_formed_export(text.splitlines()):
                return False
            candidate.write_text(text)
            results = run_matrix(kernels, candidate, args.workers)
            return all(results[name].status == status for name, status in expected.items())

        if not interesting(lines):
            print("input does not satisfy the requested outcomes", file=sys.stderr)
            return 2
        reduced = ddmin(lines, interesting, tuple(args.keep))
    final_rows: list[dict[str, object]] = []
    for line in reduced:
        if line.strip():
            final_rows.append(json.loads(line))
    final = Document(tuple(final_rows))
    if graph_mode:
        final = canonicalize(final) or final
    atomic_text(args.output, final.render())
    print(
        f"reduced {len(lines)} -> {len(final.lines)} records in {tests} tests "
        f"({'graph' if graph_mode else 'line'} mode): {args.output}"
    )
    return 0


def bench_command(config: Config, kernels: tuple[KernelSpec, ...], args: argparse.Namespace) -> int:
    return run_bench(config, args)


def findings_command(config: Config, _kernels: tuple[KernelSpec, ...], args: argparse.Namespace) -> int:
    """Group stored findings by their canonicalized case.

    Content digests count inputs; clustering counts defects.  Two findings
    whose documents canonicalize to the same bytes are the same case in a
    different presentation (extra unreachable records, a different but
    equivalent mutation path), so the report groups them under one key.
    """
    root = args.state or config.state
    findings_dir = root / "findings"
    cases = sorted(findings_dir.glob("*.ndjson"))
    if not cases:
        print(f"findings: none stored under {findings_dir}")
        return 0
    clusters: dict[str, list[dict[str, object]]] = {}
    for case in cases:
        sidecar = case.with_suffix(".json")
        metadata: dict[str, object] = {}
        if sidecar.exists():
            try:
                loaded = json.loads(sidecar.read_text())
                if isinstance(loaded, dict):
                    metadata = loaded
            except (OSError, ValueError, json.JSONDecodeError):
                metadata = {}
        entry: dict[str, object] = {"file": str(case)}
        try:
            document = Document.load(case)
        except (OSError, ValueError, json.JSONDecodeError) as failure:
            entry["error"] = str(failure)
            key = f"unreadable:{case.name}"
        else:
            canonical = canonicalize(document)
            if canonical is None:
                key = f"noncanonical:{hashlib.sha256(case.read_bytes()).hexdigest()}"
                entry["noncanonical"] = (
                    "duplicate table identifiers; reduced as-is"
                )
            else:
                key = canonical.render()
                key = f"canonical:{hashlib.sha256(key.encode()).hexdigest()}"
            entry["canonical_false"] = canonical_false_theorem(document)
        entry["sidecar"] = metadata
        clusters.setdefault(key, []).append(entry)

    ordered = sorted(clusters.items(), key=lambda item: (-len(item[1]), item[0]))
    print(f"findings: {len(cases)} inputs collapse into {len(ordered)} cluster(s)")
    report: dict[str, object] = {"schema": "pestycyd-findings-1", "clusters": []}
    for key, entries in ordered:
        first = entries[0]
        sidecar = first.get("sidecar") if isinstance(first.get("sidecar"), dict) else {}
        results = sidecar.get("results") if isinstance(sidecar.get("results"), dict) else {}
        statuses = {
            name: value.get("status") if isinstance(value, dict) else None
            for name, value in results.items()
        }
        campaign = None
        mutation = sidecar.get("mutation")
        if isinstance(mutation, dict):
            campaign = mutation.get("campaign")
        row: dict[str, object] = {
            "cluster": key,
            "findings": len(entries),
            "files": [entry["file"] for entry in entries],
            "statuses": statuses,
            "campaign": campaign,
            "canonical_false": bool(first.get("canonical_false")),
        }
        report["clusters"].append(row)
        flags = []
        if row["canonical_false"]:
            flags.append("∀P:Prop,P")
        if key.startswith("noncanonical:"):
            flags.append("noncanonical")
        suffix = f" [{', '.join(flags)}]" if flags else ""
        print(
            f"  {len(entries):4d} × {key[-12:]}{suffix} "
            f"{statuses} campaign={campaign}"
        )
    signatures: dict[tuple[object, tuple[tuple[str, object], ...]], int] = {}
    for row in report["clusters"]:
        signature = (row["campaign"], tuple(sorted(row["statuses"].items())))
        signatures[signature] = signatures.get(signature, 0) + int(row["findings"])
    sig_rows = sorted(signatures.items(), key=lambda item: -item[1])
    if sig_rows:
        print("signatures (campaign × status vector):")
        for (campaign, vector), count in sig_rows[:20]:
            rendered = ", ".join(f"{name}={status}" for name, status in vector)
            print(f"  {count:5d} × {campaign}: {rendered}")
        if len(sig_rows) > 20:
            print(f"  … {len(sig_rows) - 20} more signature(s)")
    report["signatures"] = [
        {"campaign": campaign, "statuses": dict(vector), "findings": count}
        for (campaign, vector), count in sig_rows
    ]
    if args.report:
        atomic_text(args.report, json.dumps(report, indent=2, ensure_ascii=False) + "\n")
        print(f"findings report: {args.report}")
    return 0


def parser() -> argparse.ArgumentParser:
    root = argparse.ArgumentParser(prog="pestycyd", description="Pest control for Lean kernels")
    root.add_argument("--config", type=Path, default=Path("pestycyd.toml"))
    root.add_argument("--kernel", action="append", help="select a configured kernel; repeatable")
    root.add_argument("--workers", type=int, default=None, help="parallel kernel processes per input")
    sub = root.add_subparsers(dest="command", required=True)

    command = sub.add_parser("doctor", help="probe configured kernel executables")
    command.set_defaults(function=doctor)
    command = sub.add_parser("campaigns", help="list structural campaigns and source targets")
    command.set_defaults(no_config=True)
    command.set_defaults(function=list_campaigns)

    command = sub.add_parser("generate", help="generate boundary and stress inputs")
    generators = command.add_subparsers(dest="generator", required=True)
    generator = generators.add_parser("deep-binder", help="valid deeply bound NDJSON export")
    generator.add_argument("depth", type=int)
    generator.add_argument("output", type=Path)
    generator.set_defaults(function=generate_deep_binder, no_config=True)
    generator = generators.add_parser("con-k-params", help="valid Lean K-recursor stress module")
    generator.add_argument("count", type=int)
    generator.add_argument("output", type=Path)
    generator.set_defaults(function=generate_con_k, no_config=True)
    generator = generators.add_parser(
        "app-spine", help="valid NDJSON export with a deeply nested application spine"
    )
    generator.add_argument("depth", type=int)
    generator.add_argument("output", type=Path)
    generator.set_defaults(function=generate_app_spine, no_config=True)

    command = sub.add_parser("matrix", help="run inputs through a kernel matrix")
    command.add_argument("paths", nargs="+")
    command.add_argument("--report", type=Path)
    command.add_argument("--verbose", action="store_true")
    command.set_defaults(function=matrix_command)

    command = sub.add_parser("hunt", help="run structure-aware mutation campaigns")
    command.add_argument("paths", nargs="+")
    command.add_argument("--campaign", action="append")
    command.add_argument("--iterations", type=int, default=1000)
    command.add_argument("--seed", type=int, default=0)
    command.add_argument(
        "--seed-policy",
        choices=("accepted", "consensus", "any", "all"),
        default="accepted",
        help=(
            "accepted requires every kernel to accept; consensus also permits unanimous "
            "rejection; any permits non-fatal disagreement; all also permits crash/error "
            "seeds for repair-oriented mutation"
        ),
    )
    command.add_argument(
        "--max-depth", type=int, default=3,
        help="mutate coverage-expanding inputs up to this depth",
    )
    command.add_argument(
        "--max-children", type=int, default=256,
        help="maximum mutations queued from one coverage-expanding input",
    )
    command.add_argument("--state", type=Path)
    command.add_argument(
        "--semantic-only",
        action="store_true",
        help="record semantic oracle violations and disagreements, but not crash/timeout noise",
    )
    command.add_argument(
        "--behavior-feedback",
        action="store_true",
        help=(
            "grow the queue from new normalized outcome fingerprints as well as explicit "
            "instrumentation; useful for fast release-only screening"
        ),
    )
    command.add_argument(
        "--feedback-depth-first",
        action="store_true",
        help="run children of feedback-expanding inputs before the remaining frontier",
    )
    command.add_argument(
        "--protect-final-goal",
        action="store_true",
        help=(
            "never mutate the last theorem declaration or any expression node reachable "
            "from its type"
        ),
    )
    command.add_argument(
        "--finding-expect",
        action="append",
        type=parse_expect,
        default=[],
        metavar="KERNEL=STATUS",
        help=(
            "record findings only when every requested kernel has the exact status; "
            "feedback-guided corpus growth is unchanged"
        ),
    )
    command.add_argument(
        "--finding-require-seed-change",
        action="store_true",
        help=(
            "with --finding-expect, ignore candidates whose original seed already "
            "matched the requested outcomes"
        ),
    )
    command.add_argument(
        "--budget-seconds",
        type=float,
        default=None,
        help="stop mutating after this many seconds of wall time",
    )
    command.add_argument("--verbose", action="store_true")
    command.set_defaults(function=hunt)

    command = sub.add_parser("minimize", help="delete NDJSON lines while preserving outcomes")
    command.add_argument("input", type=Path)
    command.add_argument("output", type=Path)
    command.add_argument("--expect", action="append", type=parse_expect, required=True)
    command.add_argument("--keep", action="append", default=[])
    command.add_argument(
        "--allow-malformed",
        action="store_true",
        help="allow deletion of required back-reference records when minimizing parser bugs",
    )
    command.set_defaults(function=minimize_command)

    command = sub.add_parser(
        "reduce",
        help="delete records while renumbering tables, preserving outcomes",
    )
    command.add_argument("input", type=Path)
    command.add_argument("output", type=Path)
    command.add_argument("--expect", action="append", type=parse_expect, required=True)
    command.add_argument("--keep", action="append", default=[])
    command.add_argument(
        "--allow-malformed",
        action="store_true",
        help="skip the well-formedness check on each canonicalized trial",
    )
    command.set_defaults(function=reduce_command)

    command = sub.add_parser(
        "bench",
        help="measure whether hunts reproduce pinned historical defect scenarios",
    )
    command.add_argument("scenarios", type=Path)
    command.add_argument("--filter", action="append", help="run only named scenarios; repeatable")
    command.add_argument("--report", type=Path)
    command.add_argument("--state", type=Path)
    command.set_defaults(function=bench_command)

    command = sub.add_parser(
        "findings",
        help="group stored findings by their canonicalized case",
    )
    command.add_argument("--report", type=Path)
    command.add_argument("--state", type=Path)
    command.set_defaults(function=findings_command)
    return root


def main(argv: list[str] | None = None) -> int:
    args = parser().parse_args(argv)
    try:
        if getattr(args, "no_config", False):
            return args.function(None, (), args)
        config = load_config(args.config)
        kernels = config.selected(args.kernel)
        if not kernels:
            raise ValueError("no kernels selected; enable one or pass --kernel NAME")
        if args.workers is not None and args.workers < 1:
            raise ValueError("--workers must be at least 1")
        if getattr(args, "max_depth", 1) < 1:
            raise ValueError("--max-depth must be at least 1")
        if getattr(args, "max_children", 1) < 1:
            raise ValueError("--max-children must be at least 1")
        iterations = getattr(args, "iterations", None)
        if iterations is not None and iterations < 1:
            raise ValueError("--iterations must be at least 1")
        return args.function(config, kernels, args)
    except (OSError, ValueError, tomllib.TOMLDecodeError) as failure:
        print(f"pestycyd: {failure}", file=sys.stderr)
        return 2

if __name__ == "__main__":
    raise SystemExit(main())

