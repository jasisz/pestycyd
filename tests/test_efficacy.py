from __future__ import annotations

import argparse
import contextlib
import io
import json
import shutil
import sys
import tempfile
import unittest
from pathlib import Path

from pestycyd.config import Config, KernelSpec
from pestycyd.efficacy import kills, run_efficacy, variant

META = '{"meta":{"format":{"version":"3.1.0"}}}'


def document(name: str) -> str:
    return (
        "\n".join(
            [
                META,
                f'{{"in":1,"str":{{"pre":0,"str":"{name}"}}}}',
                '{"il":1,"succ":0}',
                '{"ie":0,"sort":0}',
                '{"ie":1,"sort":1}',
                '{"def":{"all":[1],"levelParams":[],"name":1,"safety":"safe","type":1,"value":0}}',
            ]
        )
        + "\n"
    )


def checker(path: Path, refuse: str) -> Path:
    path.write_text(
        "import pathlib, sys\n"
        "data = pathlib.Path(sys.argv[1]).read_text()\n"
        f"if {refuse!r} and {refuse!r} in data:\n"
        "    print('rejected')\n"
        "    sys.exit(1)\n"
        "print('accepted')\n"
    )
    return path


class EfficacyTests(unittest.TestCase):
    def setUp(self) -> None:
        self.root = Path(tempfile.mkdtemp(prefix="pestycyd-efficacy-test-"))
        reference = checker(self.root / "reference.py", "BAD")
        self.kernels = (
            KernelSpec(
                name="official",
                command=(sys.executable, str(reference), "{file}"),
                cwd=self.root,
                timeout=10.0,
                verdict="required",
            ),
            KernelSpec(
                name="subject",
                command=(sys.executable, str(self.root / "checker.py"), "{file}"),
                cwd=self.root,
                timeout=10.0,
                verdict="required",
            ),
        )
        self.config = Config(path=self.root / "pestycyd.toml", state=self.root / "state", kernels=self.kernels)
        (self.root / "seeds").mkdir()
        (self.root / "seeds" / "bad.ndjson").write_text(document("BAD"))
        manifest = {
            "binary_name": "checker.py",
            "pristine": str(checker(self.root / "pristine.py", "BAD")),
            "mutants": [
                {"name": "lax", "binary": str(checker(self.root / "lax.py", "")), "description": "accepts all"},
                {"name": "same", "binary": str(checker(self.root / "same.py", "BAD")), "description": "no defect"},
            ],
        }
        (self.root / "mutants.json").write_text(json.dumps(manifest))
        (self.root / "plan.toml").write_text(
            "version = 1\n"
            'reference = "official"\n'
            'like = "subject"\n'
            'manifest = "mutants.json"\n'
            'paths = ["seeds"]\n'
            "iterations = 5\n"
        )

    def tearDown(self) -> None:
        shutil.rmtree(self.root, ignore_errors=True)

    def test_seed_kills_an_over_accepting_mutant_and_spares_the_control(self) -> None:
        args = argparse.Namespace(
            plan=self.root / "plan.toml", filter=None, report=self.root / "report.json", state=None
        )
        stdout = io.StringIO()
        with contextlib.redirect_stdout(stdout):
            self.assertEqual(run_efficacy(self.config, args), 0)
        log = stdout.getvalue()
        self.assertIn("efficacy lax: killed by seed bad.ndjson", log)
        self.assertIn("efficacy same: SURVIVED untested", log)
        self.assertIn("1/2 mutants killed (1 by seeds alone, 0 only by hunting)", log)
        report = json.loads((self.root / "report.json").read_text())
        self.assertEqual([row["killed_by"] for row in report["mutants"]], ["seed", None])

    def test_variant_swaps_only_the_named_binary(self) -> None:
        swapped = variant(self.kernels[1], "checker.py", "/elsewhere/m1", "mutant")
        self.assertEqual(swapped.command, (sys.executable, "/elsewhere/m1", "{file}"))
        self.assertEqual(swapped.name, "mutant")
        with self.assertRaises(ValueError):
            variant(self.kernels[0], "checker.py", "/elsewhere/m1", "mutant")

    def test_kill_requires_the_control_to_agree(self) -> None:
        self.assertTrue(kills("official", {"official": "reject", "pristine": "reject", "mutant": "accept"}))
        self.assertFalse(kills("official", {"official": "reject", "pristine": "accept", "mutant": "accept"}))
        self.assertFalse(kills("official", {"official": "reject", "pristine": "reject", "mutant": "reject"}))


if __name__ == "__main__":
    unittest.main()
