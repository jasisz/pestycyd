import random
import unittest

from pestycyd.nestgen import PRELUDE, Block, pick_major


class NestgenTests(unittest.TestCase):
    def test_blocks_render_mutual_types_and_only_used_containers(self) -> None:
        rng = random.Random(1)
        for number in range(60):
            block = Block(rng, f"N{number}")
            text = block.header()
            self.assertEqual("mutual" in block.declaration(), len(block.types) > 1)
            for name in PRELUDE:
                self.assertEqual(f"inductive {name}" in text or f"structure {name}" in text, name in block.used)

    def test_first_constructor_has_no_recursive_field_outside_containers(self) -> None:
        rng = random.Random(2)
        for number in range(60):
            block = Block(rng, f"N{number}")
            for ctors in block.ctors.values():
                base, _ = ctors[0]
                self.assertTrue(all(item[0] in {"bool", "nat", "List", "Option", "Array"} for item in base))

    def test_values_are_closed_constructor_terms_with_their_types(self) -> None:
        rng = random.Random(4)
        block = Block(rng, "N")
        values = block.values(rounds=60)
        self.assertTrue(values)
        for ty, value in values:
            self.assertRegex(value, r"^T\d\.c\d")
            self.assertTrue(ty.startswith(value.split(".")[0]))
        self.assertLessEqual(len(pick_major(values)[1]), max(1500, min(len(v) for _, v in values)))

    def test_folds_define_one_function_per_block_type_and_nested_container(self) -> None:
        rng = random.Random(0)
        for number in range(40):
            block = Block(rng, f"N{number}")
            text, top = block.folds("T0")
            self.assertEqual(top, "fT0")
            for t in block.types:
                self.assertIn(f"def f{t} : ", text)
            self.assertEqual(text.count("("), text.count(")"))
            self.assertEqual("mutual" in text, text.count("def ") > 1)

    def test_universe_blocks_spell_the_level_outside_the_block(self) -> None:
        rng = random.Random(0)
        block = next(b for b in (Block(rng, f"N{i}") for i in range(50)) if b.universe)
        self.assertIn("Type u where", block.declaration())
        self.assertNotIn(".{u}", block.declaration())
        self.assertIn("T0.{u}", block.folds("T0")[0])


if __name__ == "__main__":
    unittest.main()
