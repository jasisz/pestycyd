from __future__ import annotations

import contextlib
import io
import json
import sys
import tempfile
import unittest
from pathlib import Path

from pestycyd.bench import load_scenarios, run_bench
from pestycyd.config import Config, KernelSpec


SEED = (
    '{"meta":{"format":{"version":"3.1.0"}}}\n'
    '{"in":1,"str":{"pre":0,"str":"A"}}\n'
    '{"ie":0,"sort":0}\n'
    '{"ie":1,"bvar":0}\n'
    '{"def":{"all":[1],"levelParams":[],"name":1,"safety":"safe","type":0,"value":1}}\n'
)


class BenchTests(unittest.TestCase):
    def setUp(self) -> None:
        self.root = Path(tempfile.mkdtemp(prefix="pestycyd-bench-test-"))
        self.seed = self.root / "seed.ndjson"
        self.seed.write_text(SEED)
        # The reference accepts only the untouched seed; the broken target
        # accepts everything.  Any mutation the closedness campaign makes
        # therefore pins the historical bug-shape vector reject/accept.
        probe = self.root / "reference_probe.py"
        probe.write_text(
            "import pathlib, sys\n"
            "data = pathlib.Path(sys.argv[1]).read_bytes()\n"
            "expected = pathlib.Path(sys.argv[2]).read_bytes()\n"
            "if data == expected:\n"
            "    print('accepted')\n"
            "    sys.exit(0)\n"
            "print('rejected: mutation detected')\n"
            "sys.exit(1)\n"
        )
        broken = self.root / "broken_probe.py"
        broken.write_text("print('accepted')\n")
        self.config = Config(
            path=self.root / "pestycyd.toml",
            state=self.root / "state",
            kernels=(
                KernelSpec(
                    name="reference",
                    command=(sys.executable, str(probe), "{file}", str(self.seed)),
                    cwd=self.root,
                    timeout=10.0,
                    verdict="required",
                ),
                KernelSpec(
                    name="broken",
                    command=(sys.executable, str(broken), "{file}"),
                    cwd=self.root,
                    timeout=10.0,
                    verdict="required",
                ),
            ),
        )

    def tearDown(self) -> None:
        import shutil

        shutil.rmtree(self.root, ignore_errors=True)

    def scenario_file(self, body: str) -> Path:
        path = self.root / "scenarios.toml"
        path.write_text(body)
        return path

    def test_bench_reports_found_with_attempts_and_clusters(self) -> None:
        scenarios = self.scenario_file(
            "version = 1\n"
            "[scenario.loose-bvar]\n"
            'description = "historical bug shape"\n'
            'kernels = ["reference", "broken"]\n'
            f'seed = "{self.seed}"\n'
            'campaigns = ["closedness"]\n'
            "iterations = 4\n"
            'finding = ["reference=reject", "broken=accept"]\n'
        )
        import argparse

        args = argparse.Namespace(scenarios=scenarios, filter=None, report=self.root / "report.json", state=None)
        stdout = io.StringIO()
        with contextlib.redirect_stdout(stdout):
            exit_code = run_bench(self.config, args)
        self.assertEqual(exit_code, 0)
        report = json.loads((self.root / "report.json").read_text())
        (row,) = report["scenarios"]
        self.assertTrue(row["found"])
        self.assertGreaterEqual(row["attempts"], 1)
        self.assertIsNotNone(row["first_finding"])
        self.assertEqual(row["first_finding"]["statuses"], {"reference": "reject", "broken": "accept"})
        self.assertEqual(len(row["clusters"]), 1)
        self.assertIn("FOUND", stdout.getvalue())

    def test_scenario_validation_rejects_unknown_finding_kernel(self) -> None:
        scenarios = self.scenario_file(
            "version = 1\n"
            "[scenario.bad]\n"
            'kernels = ["reference"]\n'
            f'seed = "{self.seed}"\n'
            'finding = ["reference=reject", "ghost=accept"]\n'
        )
        with self.assertRaises(ValueError):
            load_scenarios(scenarios)

    def test_scenario_file_needs_version_one(self) -> None:
        scenarios = self.scenario_file("version = 2\n")
        with self.assertRaises(ValueError):
            load_scenarios(scenarios)

    def test_scenario_may_run_oracle_driven_without_finding_vector(self) -> None:
        scenarios = self.scenario_file(
            "version = 1\n"
            "[scenario.completeness]\n"
            'kernels = ["reference", "broken"]\n'
            f'seed = "{self.seed}"\n'
            'campaigns = ["metamorphic-let"]\n'
            "iterations = 2\n"
        )
        loaded = load_scenarios(scenarios)
        self.assertTrue(loaded["completeness"].oracle_driven)


if __name__ == "__main__":
    unittest.main()
