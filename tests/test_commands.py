from __future__ import annotations

import argparse
import contextlib
import io
import json
import sys
import tempfile
import unittest
from pathlib import Path

from pestycyd.cli import _refusal_line, findings_command, locate_command, reduce_command
from pestycyd.outcomes import Outcome
from pestycyd.config import Config, KernelSpec
from pestycyd.minimize import well_formed_export
from pestycyd.store import FindingStore


META = '{"meta":{"format":{"version":"3.1.0"}}}'
NEEDLE_DOC = "\n".join(
    [
        META,
        '{"in":1,"str":{"pre":0,"str":"NEEDLE"}}',
        '{"ie":0,"sort":0}',
        '{"ie":1,"bvar":9}',
        '{"ie":2,"bvar":0}',
        '{"def":{"all":[1],"levelParams":[],"name":1,"safety":"safe","type":0,"value":2}}',
    ]
) + "\n"


def accept_iff_needle(root: Path) -> KernelSpec:
    probe = root / "needle_probe.py"
    probe.write_text(
        "import pathlib, sys\n"
        "data = pathlib.Path(sys.argv[1]).read_text()\n"
        "if 'NEEDLE' in data:\n"
        "    print('accepted')\n"
        "    sys.exit(0)\n"
        "print('rejected: needle missing')\n"
        "sys.exit(1)\n"
    )
    return KernelSpec(
        name="guard",
        command=(sys.executable, str(probe), "{file}"),
        cwd=root,
        timeout=10.0,
        verdict="required",
    )


class ReduceTests(unittest.TestCase):
    def setUp(self) -> None:
        self.root = Path(tempfile.mkdtemp(prefix="pestycyd-reduce-test-"))
        self.kernel = accept_iff_needle(self.root)
        self.config = Config(
            path=self.root / "pestycyd.toml", state=self.root / "state", kernels=(self.kernel,)
        )

    def tearDown(self) -> None:
        import shutil

        shutil.rmtree(self.root, ignore_errors=True)

    def reduce_file(self, content: str) -> tuple[int, Path, str]:
        source = self.root / "case.ndjson"
        source.write_text(content)
        output = self.root / "reduced.ndjson"
        args = argparse.Namespace(
            input=source,
            output=output,
            expect=[("guard", "accept")],
            keep=[],
            allow_malformed=False,
            workers=None,
        )
        stdout = io.StringIO()
        with contextlib.redirect_stdout(stdout):
            code = reduce_command(self.config, (self.kernel,), args)
        return code, output, stdout.getvalue()

    def test_graph_mode_removes_mid_table_records(self) -> None:
        code, output, log = self.reduce_file(NEEDLE_DOC)
        self.assertEqual(code, 0)
        self.assertIn("graph mode", log)
        lines = output.read_text().splitlines()
        # The unused bvar record in the middle of the expression table is
        # gone and the table was renumbered densely, which plain line
        # minimization cannot do without breaking well-formedness.
        self.assertEqual(len(lines), 5)
        self.assertTrue(well_formed_export(lines))
        self.assertIn("NEEDLE", output.read_text())

    def test_duplicate_identifiers_fall_back_to_line_mode(self) -> None:
        duplicate = NEEDLE_DOC + '{"ie":2,"bvar":3}\n'
        source = self.root / "case.ndjson"
        source.write_text(duplicate)
        output = self.root / "reduced.ndjson"
        args = argparse.Namespace(
            input=source,
            output=output,
            expect=[("guard", "accept")],
            keep=[],
            allow_malformed=True,
            workers=None,
        )
        stdout = io.StringIO()
        with contextlib.redirect_stdout(stdout):
            code = reduce_command(self.config, (self.kernel,), args)
        self.assertEqual(code, 0)
        self.assertIn("falling back", stdout.getvalue())

    def test_unsatisfiable_expectation_fails(self) -> None:
        source = self.root / "case.ndjson"
        source.write_text(NEEDLE_DOC.replace("NEEDLE", "OTHER"))
        output = self.root / "reduced.ndjson"
        args = argparse.Namespace(
            input=source,
            output=output,
            expect=[("guard", "accept")],
            keep=[],
            allow_malformed=False,
            workers=None,
        )
        stderr = io.StringIO()
        with contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(stderr):
            code = reduce_command(self.config, (self.kernel,), args)
        self.assertEqual(code, 2)


THREE_DEFS = "\n".join(
    [
        META,
        '{"in":1,"str":{"pre":0,"str":"First"}}',
        '{"il":1,"succ":0}',
        '{"ie":0,"sort":0}',
        '{"ie":1,"sort":1}',
        '{"def":{"all":[1],"levelParams":[],"name":1,"safety":"safe","type":1,"value":0}}',
        '{"in":2,"str":{"pre":0,"str":"BAD"}}',
        '{"def":{"all":[2],"levelParams":[],"name":2,"safety":"safe","type":1,"value":0}}',
        '{"in":3,"str":{"pre":0,"str":"Third"}}',
        '{"def":{"all":[3],"levelParams":[],"name":3,"safety":"safe","type":1,"value":0}}',
    ]
) + "\n"


def scripted_kernel(root: Path, name: str, refuse: str) -> KernelSpec:
    probe = root / f"{name}_probe.py"
    probe.write_text(
        "import pathlib, sys\n"
        "data = pathlib.Path(sys.argv[1]).read_text()\n"
        f"if {refuse!r} and {refuse!r} in data:\n"
        f"    print('rejected: saw ' + {refuse!r})\n"
        "    sys.exit(1)\n"
        "print('accepted')\n"
        "sys.exit(0)\n"
    )
    return KernelSpec(
        name=name,
        command=(sys.executable, str(probe), "{file}"),
        cwd=root,
        timeout=10.0,
        verdict="required",
    )


class LocateTests(unittest.TestCase):
    def setUp(self) -> None:
        self.root = Path(tempfile.mkdtemp(prefix="pestycyd-locate-test-"))

    def tearDown(self) -> None:
        import shutil

        shutil.rmtree(self.root, ignore_errors=True)

    def locate(self, kernels: tuple[KernelSpec, ...]) -> tuple[int, str, dict[str, object]]:
        source = self.root / "case.ndjson"
        source.write_text(THREE_DEFS)
        args = argparse.Namespace(
            input=source,
            output=self.root / "prefix.ndjson",
            report=self.root / "locate.json",
            workers=None,
        )
        config = Config(path=self.root / "pestycyd.toml", state=self.root, kernels=kernels)
        stdout = io.StringIO()
        with contextlib.redirect_stdout(stdout):
            code = locate_command(config, kernels, args)
        return code, stdout.getvalue(), json.loads((self.root / "locate.json").read_text())

    def test_names_the_first_refused_declaration(self) -> None:
        kernels = (
            scripted_kernel(self.root, "picky", '"str":"BAD"'),
            scripted_kernel(self.root, "lax", ""),
        )
        code, log, report = self.locate(kernels)
        self.assertEqual(code, 0)
        self.assertIn("picky  reject at #2 def BAD: rejected", log)
        self.assertIn("lax    accept", log)
        self.assertEqual(report["kernels"]["picky"]["declaration"]["names"], ["BAD"])
        self.assertNotIn("declaration", report["kernels"]["lax"])
        cut = (self.root / "prefix.ndjson").read_text()
        self.assertIn("BAD", cut)
        self.assertNotIn("Third", cut)
        self.assertTrue(well_formed_export(cut.splitlines()))

    def test_refusal_before_any_declaration(self) -> None:
        kernels = (scripted_kernel(self.root, "meta", '"meta"'),)
        _code, log, report = self.locate(kernels)
        self.assertIn("before any declaration", log)
        self.assertIsNone(report["kernels"]["meta"]["declaration"])


    def test_refusal_line_prefers_the_reason(self) -> None:
        def outcome(output: str) -> Outcome:
            return Outcome(status="reject", seconds=0.0, exit_code=1, verdict=None, output=output)

        panic = (
            "[0/6 0ms +0ms]\n"
            "thread 'main-worker' (1) panicked at src/inductive.rs:166:13:\n"
            "for inductive type M1,\n"
            "run with `-h` or `--help` for help\n"
        )
        self.assertEqual(_refusal_line(outcome(panic)), "for inductive type M1,")
        lean = "Lean default kernel: while replaying 'f':\n(kernel) invalid projection\n  x.1\n"
        self.assertEqual(_refusal_line(outcome(lean)), "(kernel) invalid projection")
        self.assertEqual(_refusal_line(outcome("progress\ndone\n")), "done")

class FindingsTests(unittest.TestCase):
    def setUp(self) -> None:
        self.root = Path(tempfile.mkdtemp(prefix="pestycyd-findings-test-"))

    def tearDown(self) -> None:
        import shutil

        shutil.rmtree(self.root, ignore_errors=True)

    def test_same_case_in_two_presentations_clusters_together(self) -> None:
        minimal = (
            META + "\n"
            '{"in":1,"str":{"pre":0,"str":"A"}}\n'
            '{"ie":0,"sort":0}\n'
            '{"ie":1,"bvar":0}\n'
            '{"def":{"all":[1],"levelParams":[],"name":1,"safety":"safe","type":0,"value":1}}\n'
        )
        noisy = (
            META + "\n"
            '{"in":1,"str":{"pre":0,"str":"A"}}\n'
            '{"in":2,"str":{"pre":0,"str":"junk"}}\n'
            '{"ie":0,"sort":0}\n'
            '{"ie":1,"bvar":0}\n'
            '{"ie":2,"bvar":7}\n'
            '{"def":{"all":[1],"levelParams":[],"name":1,"safety":"safe","type":0,"value":1}}\n'
        )
        store = FindingStore(self.root)
        store.save(
            minimal,
            {"mutation": {"campaign": "closedness"}, "results": {"a": {"status": "reject"}, "b": {"status": "accept"}}},
        )
        store.save(
            noisy,
            {"mutation": {"campaign": "closedness"}, "results": {"a": {"status": "reject"}, "b": {"status": "accept"}}},
        )
        config = Config(path=self.root / "pestycyd.toml", state=self.root, kernels=())
        args = argparse.Namespace(state=self.root, report=self.root / "report.json")
        stdout = io.StringIO()
        with contextlib.redirect_stdout(stdout):
            code = findings_command(config, (), args)
        self.assertEqual(code, 0)
        self.assertIn("1 cluster", stdout.getvalue())
        report = json.loads((self.root / "report.json").read_text())
        (cluster,) = report["clusters"]
        self.assertEqual(cluster["findings"], 2)
        self.assertEqual(cluster["statuses"], {"a": "reject", "b": "accept"})
        self.assertEqual(cluster["campaign"], "closedness")

    def test_reports_empty_state(self) -> None:
        config = Config(path=self.root / "pestycyd.toml", state=self.root, kernels=())
        args = argparse.Namespace(state=self.root, report=None)
        stdout = io.StringIO()
        with contextlib.redirect_stdout(stdout):
            code = findings_command(config, (), args)
        self.assertEqual(code, 0)
        self.assertIn("none stored", stdout.getvalue())


if __name__ == "__main__":
    unittest.main()
