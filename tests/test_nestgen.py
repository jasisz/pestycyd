import random
import unittest

from pestycyd.nestgen import PRELUDE, Block, pick_major


class NestgenTests(unittest.TestCase):
    def test_blocks_render_mutual_types_and_only_used_containers(self) -> None:
        rng = random.Random(1)
        for number in range(60):
            block = Block(rng, f"N{number}")
            text = block.header()
            self.assertEqual("mutual" in text, len(block.types) > 1)
            for name in PRELUDE:
                self.assertEqual(f"inductive {name}" in text or f"structure {name}" in text, name in block.used)

    def test_first_constructor_has_no_recursive_field_outside_containers(self) -> None:
        rng = random.Random(2)
        for number in range(60):
            block = Block(rng, f"N{number}")
            for ctors in block.ctors.values():
                base, _ = ctors[0]
                self.assertTrue(all(item[0] in {"bool", "nat", "List", "Option", "Array"} for item in base))

    def test_values_are_closed_constructor_terms(self) -> None:
        rng = random.Random(4)
        block = Block(rng, "N")
        values = block.values(rounds=60)
        self.assertTrue(values)
        for value in values:
            self.assertRegex(value, r"^T\d\.c\d")
        self.assertLessEqual(len(pick_major(values)), max(1500, min(len(v) for v in values)))


if __name__ == "__main__":
    unittest.main()
