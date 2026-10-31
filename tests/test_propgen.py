import random
import unittest

from pestycyd.indgen import Generated
from pestycyd.propgen import SORTS, TWIN, Family


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

    def test_forged_source_mirrors_t0_in_a_never_zero_sort_and_uses_its_large_recursor(self) -> None:
        rng = random.Random(0)
        family = next(f for f in (Family(rng, f"P{i}") for i in range(100)) if not f.mutual and f.ctors["T0"])
        text = family.source(forge=True)
        self.assertIn(f"inductive {TWIN}", text)
        self.assertIn(f": Sort (max 1 ", text.split(f"inductive {TWIN}")[1].split("where")[0])
        self.assertEqual(text.count(f"| c"), 2 * len(family.ctors["T0"]))
        self.assertIn(f"{TWIN}.rec (motive := fun", text)
        self.assertEqual(family.use().count("(by intros; exact Nat)"), len(family.ctors["T0"]))

    def test_forged_variant_is_an_accept_only_when_lean_granted_large_elimination(self) -> None:
        valid = Generated("G", "", "x", forged="forged", forged_valid=True)
        self.assertEqual((valid.accepts(), valid.rejects()), (["forged"], []))
        forged = Generated("G", "", "x", forged="forged", forged_valid=False)
        self.assertEqual((forged.accepts(), forged.rejects()), ([], ["forged"]))


if __name__ == "__main__":
    unittest.main()
