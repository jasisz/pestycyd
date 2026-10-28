from __future__ import annotations

import unittest
from pathlib import Path

from pestycyd.minimize import well_formed_export
from pestycyd.ndjson import Document


class CorpusTests(unittest.TestCase):
    def test_every_checked_in_case_is_valid_ndjson(self) -> None:
        corpus = Path(__file__).resolve().parents[1] / "corpus"
        cases = sorted(corpus.rglob("*.ndjson"))
        self.assertGreaterEqual(len(cases), 10)
        for case in cases:
            with self.subTest(case=case.name):
                self.assertNotIn("", case.read_text().splitlines())
                self.assertTrue(Document.load(case).lines)
                self.assertTrue(well_formed_export(case.read_text().splitlines()))

if __name__ == "__main__":
    unittest.main()
