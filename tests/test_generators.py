from __future__ import annotations

import json
import unittest

from pestycyd.generators import app_spine, con_k_params, deep_binder


class GeneratorTests(unittest.TestCase):
    def test_deep_binder_is_ndjson_with_requested_depth(self) -> None:
        lines = [json.loads(line) for line in deep_binder(4).splitlines()]
        foralls = [line for line in lines if "forallE" in line]
        lambdas = [line for line in lines if "lam" in line]
        self.assertEqual(len(foralls), 5)
        self.assertEqual(len(lambdas), 5)
        self.assertIn("thm", lines[-1])

    def test_con_k_generator_has_every_parameter(self) -> None:
        source = con_k_params(4)
        self.assertIn("(P0 : Prop)", source)
        self.assertIn("(P3 : Prop)", source)
        self.assertIn("collapse", source)

    def test_app_spine_is_well_formed_and_matches_manual_spine(self) -> None:
        from pestycyd.minimize import well_formed_export

        text = app_spine(50)
        self.assertTrue(well_formed_export(text.splitlines()))
        rows = [json.loads(line) for line in text.splitlines()]
        # 2 records per spine level plus the 18 header records and the def.
        self.assertEqual(len(rows), 18 + 2 * 50 + 1)
        self.assertEqual(rows[-1]["def"]["name"], 3)


if __name__ == "__main__":
    unittest.main()
