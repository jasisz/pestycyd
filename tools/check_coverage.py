#!/usr/bin/env python3
"""Which reference-kernel checks do the campaigns actually reach?

Samples mutations from every campaign over the given seeds (operator-
balanced, like a hunt), runs each through one kernel, and tallies its
rejection reasons per campaign.  A check no campaign triggers is a class
of defect the fuzzer cannot find in any checker.

Usage: check_coverage.py CONFIG KERNEL PER_CAMPAIGN OUT.json SEED...
"""

import collections
import json
import random
import re
import sys
import tempfile
from pathlib import Path

from pestycyd.campaigns import CAMPAIGNS
from pestycyd.cli import operator_balanced
from pestycyd.config import load_config
from pestycyd.ndjson import Document, files
from pestycyd.runner import run_kernel


def reason(output):
    kernel = re.search(r"\(kernel\) ([^\n]+)", output)
    if kernel:
        text = kernel.group(1)
    else:
        lines = [line.strip() for line in output.splitlines() if line.strip()]
        text = lines[-1] if lines else "?"
    return re.sub(r"'[^']*'|`[^`]*`|\b\d+\b", "_", text)[:80]


def main():
    config_path, kernel_name, per_campaign, out = sys.argv[1:5]
    (kernel,) = load_config(Path(config_path)).selected([kernel_name])
    seeds = [Document.load(path) for path in files(sys.argv[5:])]
    rng = random.Random(0)
    report = {}
    with tempfile.TemporaryDirectory() as directory:
        candidate = Path(directory) / "candidate.ndjson"
        for name, campaign in CAMPAIGNS.items():
            pool = [(document, mutation) for document in seeds for mutation in campaign.generate(document)]
            order = operator_balanced([mutation for _, mutation in pool], rng)
            owner = {id(mutation): document for document, mutation in pool}
            tally = collections.Counter()
            for mutation in order[: int(per_campaign)]:
                candidate.write_text(owner[id(mutation)].mutated(mutation).render())
                outcome = run_kernel(kernel, candidate)
                tally["ACCEPT" if outcome.status == "accept" else reason(outcome.output)] += 1
            report[name] = dict(tally.most_common())
            print(name, dict(tally.most_common(4)), flush=True)
    Path(out).write_text(json.dumps(report, indent=2) + "\n")


if __name__ == "__main__":
    main()
