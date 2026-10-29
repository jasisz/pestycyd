from __future__ import annotations

import unittest
from pathlib import Path

from pestycyd.minimize import well_formed_export
from pestycyd.ndjson import Document


# Documents whose point is a broken table: a re-bound index or a dangling reference.
MALFORMED_BY_DESIGN = {
    "leads/pestka-lean4lean-dup-ie-lastwins.ndjson",
    "probes/malformed/sortbig.ndjson",
    "probes/malformed/sortneg.ndjson",
    "probes/qred-bad.ndjson",
}


class CorpusTests(unittest.TestCase):
    def test_every_checked_in_case_is_valid_ndjson(self) -> None:
        corpus = Path(__file__).resolve().parents[1] / "corpus"
        cases = sorted(corpus.rglob("*.ndjson"))
        self.assertGreaterEqual(len(cases), 10)
        for case in cases:
            with self.subTest(case=case.name):
                self.assertNotIn("", case.read_text().splitlines())
                self.assertTrue(Document.load(case).lines)
                malformed = case.relative_to(corpus).as_posix() in MALFORMED_BY_DESIGN
                self.assertEqual(well_formed_export(case.read_text().splitlines()), not malformed)

if __name__ == "__main__":
    unittest.main()
