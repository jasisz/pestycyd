"""Generate kernel-checked inductives and terms, then export them as NDJSON."""

from __future__ import annotations

import argparse
import json
import os
import re
import shutil
import subprocess
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

PINNED_LEAN = Path.home() / ".elan/toolchains/leanprover--lean4---v4.35.0/bin/lean"


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("output", type=Path, help="new output directory")
    parser.add_argument("--seed", type=int, default=17)
    parser.add_argument("--blocks", type=int, default=40)
    parser.add_argument("--terms", type=int, default=150)
    parser.add_argument("--rec-terms", type=int, default=0,
                        help="additional theorems that reduce a generated recursor")
    parser.add_argument("--hide", type=int, default=0,
                        help="percent of constructor fields hidden behind a beta, let or id redex")
    parser.add_argument("--rich", action="store_true",
                        help="two universe parameters, richer sorts and Nat indices")
    parser.add_argument("--limit", type=int, help="maximum exports from each category")
    parser.add_argument("--workers", type=int, default=4)
    parser.add_argument("--lean", default=str(PINNED_LEAN) if PINNED_LEAN.exists() else "lean")
    parser.add_argument("--leanexport")
    args = parser.parse_args()
    if min(args.seed, args.blocks, args.terms, args.rec_terms) < 0:
        parser.error("seed, blocks, terms and rec-terms must be nonnegative")
    if args.workers < 1 or (args.limit is not None and args.limit < 0):
        parser.error("workers must be positive and limit must be nonnegative")
    prefix = subprocess.check_output([args.lean, "--print-prefix"], text=True).strip()
    leanexport = args.leanexport or str(Path(prefix) / "bin" / "leanexport")
    if not Path(leanexport).is_file() and shutil.which(leanexport) is None:
        parser.error(f"leanexport not found at {leanexport}; pass --leanexport")
    args.output.mkdir(parents=True, exist_ok=False)
    build = args.output / "build"
    build.mkdir()
    for name in ("Gen.lean", "GenInd.lean"):
        shutil.copyfile(Path(__file__).with_name(name), build / name)

    env = {**os.environ, "LEAN_PATH": f"{build}:{prefix}/lib/lean"}
    runner = f'''import GenInd
open Lean Meta
set_option Elab.async false
set_option maxRecDepth 2000
run_meta do
  let (indGood, targets, rejected) ← PestycydGen.runInd {args.seed} {args.blocks} {args.hide} {'true' if args.rich else 'false'}
  let (termGood, termBad) ← PestycydGen.run {args.seed + 1} {args.terms} indGood targets
  let recGood ← PestycydGen.runRec {args.seed + 2} {args.rec_terms} indGood targets
  IO.FS.writeFile "inductive.names" (String.intercalate "\\n" (indGood.toList.map toString))
  IO.FS.writeFile "good.names" (String.intercalate "\\n" (termGood.toList.map toString))
  IO.FS.writeFile "bad.names" (String.intercalate "\\n" (termBad.toList.map toString))
  IO.FS.writeFile "rec.names" (String.intercalate "\\n" (recGood.toList.map toString))
  IO.FS.writeFile "rejected.count" (toString rejected)
'''
    (build / "Run.lean").write_text(runner)
    for module in ("Gen", "GenInd", "Run"):
        subprocess.run(
            [args.lean, "-o", f"{module}.olean", f"{module}.lean"],
            cwd=build, env=env, check=True,
        )

    names = {
        "inductive": [n for n in (build / "inductive.names").read_text().splitlines()
                      if re.fullmatch(r"T[0-9]+", n.rsplit(".", 1)[-1])],
        "good": (build / "good.names").read_text().splitlines(),
        "bad": (build / "bad.names").read_text().splitlines(),
        "rec": (build / "rec.names").read_text().splitlines(),
    }
    jobs = [(kind, name) for kind, group in names.items()
            for name in (group[:args.limit] if args.limit is not None else group)]
    for kind in names:
        (args.output / kind).mkdir()

    def export(job: tuple[str, str]) -> tuple[str, str | None, bool]:
        kind, name = job
        try:
            result = subprocess.run(
                [leanexport, "Run", "--", name], cwd=build, env=env,
                capture_output=True, text=True, timeout=120,
            )
        except (OSError, subprocess.TimeoutExpired) as exc:
            return kind, f"{name}: {exc}", False
        if result.returncode or not result.stdout:
            return kind, f"{name}: {result.stderr.strip()[:200]}", False
        (args.output / kind / f"{name.replace('.', '_')}.ndjson").write_text(result.stdout)
        return kind, None, '"PestycydInd"' in result.stdout

    with ThreadPoolExecutor(max_workers=args.workers) as pool:
        results = list(pool.map(export, jobs))
    errors = [error for _, error, _ in results if error]
    summary = {
        "seed": args.seed,
        "hide": args.hide,
        "rich": args.rich,
        "blocks_tried": args.blocks,
        "blocks_rejected": int((build / "rejected.count").read_text()),
        "inductive_types": len(names["inductive"]),
        "terms_accepted": len(names["good"]),
        "terms_rejected": len(names["bad"]),
        "recursor_theorems": len(names["rec"]),
        "exports": {kind: sum(k == kind and error is None for k, error, _ in results)
                    for kind in names},
        "exports_with_generated_inductive": {
            kind: sum(k == kind and used for k, _, used in results) for kind in names
        },
        "errors": errors,
    }
    (args.output / "summary.json").write_text(json.dumps(summary, indent=2) + "\n")
    print(json.dumps(summary, indent=2))
    if errors:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
