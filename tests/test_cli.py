from __future__ import annotations

import contextlib
import io
import json
import sys
import tempfile
import unittest
from pathlib import Path

from pestycyd.cli import main


class CliTests(unittest.TestCase):
    def test_matrix_command_does_not_require_hunt_only_arguments(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            case = root / "case.ndjson"
            case.write_text("{}\n")
            config = root / "pestycyd.toml"
            command = [sys.executable, "-c", "print('accepted')", "{file}"]
            config.write_text(
                "version=1\n[kernels.fake]\n"
                f"command={json.dumps(command)}\nverdict='required'\n"
            )
            with contextlib.redirect_stdout(io.StringIO()):
                result = main(["--config", str(config), "matrix", str(case)])
        self.assertEqual(result, 0)

    def test_matrix_baseline_reports_changed_verdicts(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            case = root / "case.ndjson"
            case.write_text("{}\n")
            config = root / "pestycyd.toml"
            report = root / "before.json"

            def run(word: str, *extra: str) -> tuple[int, str]:
                code = 0 if word == "accepted" else 1
                script = f"print('{word}'); raise SystemExit({code})"
                command = [sys.executable, "-c", script, "{file}"]
                config.write_text(
                    "version=1\n[kernels.fake]\n"
                    f"command={json.dumps(command)}\nverdict='required'\n"
                )
                output = io.StringIO()
                with contextlib.redirect_stdout(output):
                    result = main(["--config", str(config), "matrix", str(case), *extra])
                return result, output.getvalue()

            self.assertEqual(run("accepted", "--report", str(report))[0], 0)
            result, output = run("accepted", "--baseline", str(report))
            self.assertEqual(result, 0)
            self.assertNotIn("CHANGED", output)
            result, output = run("rejected", "--baseline", str(report))
        self.assertEqual(result, 1)
        self.assertIn("fake accept->reject", output)

    def test_renumber_closes_table_gaps(self) -> None:
        gapped = [
            '{"meta":{}}',
            '{"in":1,"str":{"pre":0,"str":"P"}}',
            '{"ie":5,"sort":0}',
            '{"axiom":{"all":[1],"levelParams":[],"name":1,"type":5}}',
        ]
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            source = root / "gapped.ndjson"
            target = root / "dense.ndjson"
            source.write_text("\n".join(gapped) + "\n")
            with contextlib.redirect_stdout(io.StringIO()):
                result = main(["renumber", str(source), str(target)])
            rows = [json.loads(line) for line in target.read_text().splitlines()]
        self.assertEqual(result, 0)
        self.assertEqual(rows[2], {"ie": 0, "sort": 0})
        self.assertEqual(rows[3]["axiom"]["type"], 0)

    def test_campaign_listing_needs_no_configuration(self) -> None:
        with contextlib.redirect_stdout(io.StringIO()):
            result = main(["campaigns"])
        self.assertEqual(result, 0)


if __name__ == "__main__":
    unittest.main()
