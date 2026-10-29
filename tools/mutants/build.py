#!/usr/bin/env python3
"""Build seeded-defect variants of a checker from a mutant spec.

Copies SOURCE once into OUT/work, then for each mutant applies its exact
text replacement, runs the spec's build command, copies the binary to
OUT/<name>, and restores the file.  The unmodified build is copied to
OUT/pristine first: `pestycyd efficacy` needs it as the control that
tells seeded defects apart from the checker's own divergences.

OUT/mutants.json lists every binary with its description and history.

Usage: build.py SPEC.toml SOURCE OUT [--only NAME ...]
"""

import argparse
import json
import shutil
import subprocess
import sys
import tomllib
from pathlib import Path


def build(work, spec, target):
    subprocess.run(spec["build"], cwd=work, check=True)
    shutil.copy2(work / spec["binary"], target)


def main():
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("spec", type=Path)
    parser.add_argument("source", type=Path)
    parser.add_argument("out", type=Path)
    parser.add_argument("--only", action="append", default=[])
    args = parser.parse_args()

    spec = tomllib.loads(args.spec.read_text())
    if spec.get("version") != 1:
        sys.exit("spec needs version = 1")
    mutants = spec["mutant"]
    unknown = set(args.only).difference(mutants)
    if unknown:
        sys.exit(f"unknown mutants: {', '.join(sorted(unknown))}")

    out = args.out.resolve()
    work = out / "work"
    if not work.exists():
        shutil.copytree(args.source, work, symlinks=True, ignore=shutil.ignore_patterns(".git"))
    print("building pristine", flush=True)
    build(work, spec, out / "pristine")

    manifest = {
        "source": str(args.source.resolve()),
        "binary_name": Path(spec["binary"]).name,
        "pristine": str(out / "pristine"),
        "mutants": [],
    }
    for name, mutant in mutants.items():
        if args.only and name not in args.only:
            continue
        path = work / mutant["file"]
        original = path.read_text()
        count = original.count(mutant["old"])
        if count != 1:
            sys.exit(f"{name}: `old` occurs {count} times in {mutant['file']}, expected once")
        print(f"building {name}", flush=True)
        path.write_text(original.replace(mutant["old"], mutant["new"]))
        try:
            build(work, spec, out / name)
        finally:
            path.write_text(original)
        manifest["mutants"].append(
            {
                "name": name,
                "binary": str(out / name),
                "file": mutant["file"],
                "description": mutant["description"],
                "history": mutant.get("history"),
            }
        )
    (out / "mutants.json").write_text(json.dumps(manifest, indent=2) + "\n")
    print(f"{len(manifest['mutants'])} mutants: {out / 'mutants.json'}")


if __name__ == "__main__":
    main()
