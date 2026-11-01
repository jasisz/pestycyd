"""Run every configured kernel over scale-ladder exports and record verdict, time and crash."""

from __future__ import annotations

import argparse
import json
import os
import signal
import subprocess
import time
import tomllib
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("files", nargs="+", type=Path)
    ap.add_argument("--config", type=Path, default=Path(".pestycyd/all-checkers.toml"))
    ap.add_argument("--kernel", action="append")
    ap.add_argument("--timeout", type=float, default=60)
    ap.add_argument("--workers", type=int, default=4)
    ap.add_argument("--out", type=Path, required=True)
    a = ap.parse_args()
    cfg = tomllib.loads(a.config.read_text())
    kernels = {k: v for k, v in cfg["kernels"].items() if not a.kernel or k in a.kernel}
    jobs = [(f, k) for f in a.files for k in kernels]

    def run(job):
        f, k = job
        spec = kernels[k]
        cmd = [str(f) if c == "{file}" else c for c in spec["command"]]
        env = {**os.environ, **{k2: v.replace("{file}", str(f)) for k2, v in spec.get("env", {}).items()}}
        t0 = time.monotonic()
        try:
            p = subprocess.run(cmd, capture_output=True, text=True, timeout=a.timeout, env=env)
            dt = time.monotonic() - t0
            rc = p.returncode
            tail = (p.stderr + p.stdout)[-300:].replace("\n", " | ")
            status = (f"signal:{signal.Signals(-rc).name}" if rc < 0 else f"exit:{rc}")
        except subprocess.TimeoutExpired:
            dt, status, tail = a.timeout, "timeout", ""
        return {"file": f.name, "kernel": k, "status": status, "time": round(dt, 2), "tail": tail}

    with ThreadPoolExecutor(a.workers) as pool, a.out.open("w") as out:
        for r in pool.map(run, jobs):
            out.write(json.dumps(r) + "\n")
            out.flush()


if __name__ == "__main__":
    main()
