import random
import unittest

from pestycyd.propgen import SORTS, Family


class PropgenTests(unittest.TestCase):
    def test_sources_lift_the_resulting_universe_check_and_use_known_sorts(self) -> None:
        rng = random.Random(1)
        for number in range(80):
            family = Family(rng, f"P{number}")
            text = family.source()
            self.assertIn("set_option bootstrap.inductiveCheckResultingUniverse false", text)
            self.assertIn(family.sort, SORTS)
            self.assertEqual("mutual" in text, family.mutual)
            for t in family.types:
                self.assertIn(f"inductive {t}", text)

    def test_mutual_blocks_take_parameters_through_variable(self) -> None:
        rng = random.Random(3)
        family = next(f for f in (Family(rng, f"P{i}") for i in range(200)) if f.mutual and f.params)
        text = family.source()
        self.assertIn("variable (", text)
        self.assertNotIn("inductive T0 (", text)

    def test_index_values_only_use_alpha_through_fields(self) -> None:
        rng = random.Random(5)
        family = Family(rng, "P")
        self.assertIsNone(family.value("α", []))
        self.assertIn(family.value("α", [("x0", "α")]), {"x0", None})


if __name__ == "__main__":
    unittest.main()
