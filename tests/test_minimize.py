import unittest

from pestycyd.minimize import ddmin, well_formed_export


class MinimizeTests(unittest.TestCase):
    def test_ddmin_keeps_only_required_lines(self) -> None:
        lines = ["header", "noise-a", "needle", "noise-b"]
        result = ddmin(lines, lambda trial: "header" in trial and "needle" in trial, ("header",))
        self.assertEqual(result, ["header", "needle"])

    def test_well_formed_export_requires_complete_back_references(self) -> None:
        complete = [
            '{"meta":{}}',
            '{"in":1,"str":{"pre":0,"str":"P"}}',
            '{"ie":0,"sort":0}',
            '{"axiom":{"all":[1],"levelParams":[],"name":1,"type":0}}',
        ]
        self.assertTrue(well_formed_export(complete))
        self.assertFalse(well_formed_export(complete[:2]))
        self.assertFalse(well_formed_export([complete[0], complete[1], complete[3]]))

    def test_well_formed_export_rejects_gapped_tables(self) -> None:
        lines = [
            '{"in":1,"str":{"pre":0,"str":"P"}}',
            '{"ie":1,"sort":0}',
            '{"axiom":{"all":[1],"levelParams":[],"name":1,"type":1}}',
        ]
        self.assertFalse(well_formed_export(lines))


if __name__ == "__main__":
    unittest.main()
