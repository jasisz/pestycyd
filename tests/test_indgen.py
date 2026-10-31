import json
import random
import unittest

from pestycyd.indgen import (
    OFFSET,
    Ctor,
    Family,
    Field,
    Generated,
    build_values,
    declaration,
    random_family,
    use_theorem,
)

TREE = Family(
    name="G",
    sort="Type",
    params=("Type",),
    indices=("Bool",),
    ctors=(
        Ctor((Field("param"),), ("true",)),
        Ctor((Field("bool"), Field("rec", ("true",)), Field("refl", ("true",))), ("#0",)),
        Ctor((Field("nested", ("true",)),), ("false",)),
    ),
)


class IndgenTests(unittest.TestCase):
    def test_declaration_renders_fields_and_result_indices(self) -> None:
        text = declaration(TREE)
        self.assertIn("inductive T (α0 : Type) : Bool → Type where", text)
        self.assertIn("| c0 : (x0 : α0) → T α0 true", text)
        self.assertIn("| c1 : (x0 : Bool) → (x1 : T α0 true) → (x2 : Bool → T α0 true) → T α0 x0", text)
        self.assertIn("| c2 : (x0 : List (T α0 true)) → T α0 false", text)

    def test_fold_counts_constructor_numbers_through_children(self) -> None:
        values = build_values(random.Random(3), TREE, rounds=40)
        self.assertTrue(values)
        for value in values:
            self.assertEqual(value.fold, self._fold(value))

    def _fold(self, value) -> int:  # type: ignore[no-untyped-def]
        number = int(value.lean.split()[0].removeprefix("T.c"))
        return number + 1 + sum(self._fold(child) for child in value.children)

    def test_use_theorem_supplies_one_motive_and_minor_pair_per_nested_occurrence(self) -> None:
        major = build_values(random.Random(3), TREE, rounds=40)[-1]
        theorem = use_theorem(TREE, major, prop=False)
        self.assertIn("(fun _ _ => Nat) (fun _ => Nat)", theorem)
        self.assertIn("(0) (fun _ _ a b => Nat.add a b)", theorem)
        self.assertTrue(theorem.endswith(f"= {OFFSET + major.fold} := rfl"))

    def test_random_families_keep_a_base_constructor(self) -> None:
        rng = random.Random(7)
        for number in range(100):
            family = random_family(rng, f"G{number}")
            base = family.ctors[0]
            self.assertFalse(any(item.kind in {"rec", "refl", "nested"} for item in base.fields))

    def test_shifted_bumps_only_the_result_literal(self) -> None:
        lines = [
            {"meta": {}},
            {"ie": 0, "natVal": str(OFFSET + 4)},
            {"ie": 1, "natVal": "4"},
        ]
        export = "".join(json.dumps(line) + "\n" for line in lines)
        shifted = Generated("G", "", export, fold=4).shifted()
        assert shifted is not None
        values = [json.loads(line).get("natVal") for line in shifted.splitlines()]
        self.assertEqual(values, [None, str(OFFSET + 5), "4"])
        self.assertIsNone(Generated("G", "", export, fold=None).shifted())

    def test_rejects_bump_each_theorem_result_once(self) -> None:
        lines = [{"ie": 0, "natVal": str(OFFSET + 4)}, {"ie": 1, "natVal": "2000009"}]
        export = "".join(json.dumps(line) + "\n" for line in lines)
        rejects = Generated("G", "", export, fold=4, results=(2000009, 77)).rejects()
        values = [[json.loads(line)["natVal"] for line in text.splitlines()] for text in rejects]
        self.assertEqual(values, [[str(OFFSET + 5), "2000009"], [str(OFFSET + 4), "2000010"]])


if __name__ == "__main__":
    unittest.main()
