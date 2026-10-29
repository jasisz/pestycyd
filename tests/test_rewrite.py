import unittest

from pestycyd.ndjson import Document
from pestycyd.minimize import well_formed_export
from pathlib import Path

from pestycyd.rewrite import (
    _declared,
    _name_strings,
    canonical_false_theorem,
    canonicalize,
    prelude_lines,
    renumber,
)


META = {"meta": {"format": {"version": "3.1.0"}}}


def def_line(name: int, type_id: int, value_id: int) -> dict[str, object]:
    return {
        "def": {
            "all": [name],
            "levelParams": [],
            "name": name,
            "safety": "safe",
            "type": type_id,
            "value": value_id,
        }
    }


class CanonicalizeTests(unittest.TestCase):
    def test_drops_unreachable_records_and_renumbers(self) -> None:
        document = Document(
            (
                META,
                {"in": 1, "str": {"pre": 0, "str": "used"}},
                {"in": 2, "str": {"pre": 0, "str": "junk"}},
                {"ie": 0, "sort": 0},
                {"ie": 1, "bvar": 0},
                {"ie": 2, "bvar": 1},  # unreachable
                def_line(1, 0, 1),
            )
        )
        canonical = canonicalize(document)
        assert canonical is not None
        lines = canonical.render().splitlines()
        self.assertTrue(well_formed_export(lines))
        self.assertEqual(len(canonical.lines), 5)
        self.assertNotIn("junk", canonical.render())
        # The surviving bvar kept its meaning: still bvar 0, still the value.
        self.assertEqual(canonical.lines[3], {"ie": 1, "bvar": 0})

    def test_equivalent_presentations_canonicalize_identically(self) -> None:
        base = [
            META,
            {"in": 1, "str": {"pre": 0, "str": "A"}},
            {"ie": 0, "sort": 0},
            {"ie": 1, "bvar": 0},
            def_line(1, 0, 1),
        ]
        noisy = [
            META,
            {"in": 1, "str": {"pre": 0, "str": "A"}},
            {"in": 2, "str": {"pre": 0, "str": "noise"}},
            {"ie": 0, "sort": 0},
            {"ie": 1, "bvar": 0},
            {"ie": 2, "sort": 1},
            def_line(1, 0, 1),
        ]
        left = canonicalize(Document(tuple(base)))
        right = canonicalize(Document(tuple(noisy)))
        assert left is not None and right is not None
        self.assertEqual(left.render(), right.render())

    def test_duplicate_table_identifiers_are_left_alone(self) -> None:
        document = Document(
            (
                META,
                {"ie": 0, "sort": 0},
                {"ie": 0, "sort": 1},  # intern-table shadowing shape
                def_line(1, 0, 0),
            )
        )
        self.assertIsNone(canonicalize(document))
        self.assertIsNone(renumber(document))

    def test_is_idempotent(self) -> None:
        document = Document(
            (
                META,
                {"in": 1, "str": {"pre": 0, "str": "A"}},
                {"in": 2, "str": {"pre": 0, "str": "B"}},
                {"ie": 0, "sort": 0},
                {"ie": 1, "bvar": 0},
                {"ie": 2, "bvar": 1},  # unreachable
                def_line(2, 0, 1),
            )
        )
        once = canonicalize(document)
        assert once is not None
        twice = canonicalize(once)
        assert twice is not None
        self.assertEqual(once.render(), twice.render())

    def test_inductive_internals_are_kept_and_renumbered(self) -> None:
        document = Document(
            (
                META,
                {"in": 1, "str": {"pre": 0, "str": "Box"}},
                {"in": 2, "str": {"pre": 1, "str": "mk"}},
                {"in": 3, "str": {"pre": 1, "str": "rec"}},
                {"in": 4, "str": {"pre": 0, "str": "junk"}},
                {"ie": 0, "sort": 0},
                {
                    "inductive": {
                        "types": [
                            {
                                "all": [1],
                                "ctors": [2],
                                "levelParams": [],
                                "name": 1,
                                "numIndices": 0,
                                "numNested": 0,
                                "numParams": 0,
                                "type": 0,
                            }
                        ],
                        "ctors": [
                            {
                                "induct": 1,
                                "levelParams": [],
                                "name": 2,
                                "numFields": 0,
                                "numParams": 0,
                                "type": 0,
                            }
                        ],
                        "recs": [
                            {
                                "all": [1],
                                "levelParams": [],
                                "name": 3,
                                "numIndices": 0,
                                "numMinors": 1,
                                "numMotives": 1,
                                "numParams": 0,
                                "rules": [{"ctor": 2, "nfields": 0, "rhs": 0}],
                                "type": 0,
                            }
                        ],
                    }
                },
            )
        )
        canonical = canonicalize(document)
        assert canonical is not None
        self.assertTrue(well_formed_export(canonical.render().splitlines()))
        self.assertNotIn("junk", canonical.render())
        self.assertIn("mk", canonical.render())


class QuotRenumberTests(unittest.TestCase):
    def test_quot_records_follow_renumbered_names_and_expressions(self) -> None:
        # Name 3 is interned before name 2, as in an export whose quot
        # records were reordered: dense renumbering swaps them.
        document = Document(
            (
                {"meta": {"format": {"version": "3.1.0"}}},
                {"in": 1, "str": {"pre": 0, "str": "u"}},
                {"il": 1, "param": 1},
                {"in": 3, "str": {"pre": 0, "str": "Quot"}},
                {"ie": 5, "sort": 1},
                {"quot": {"kind": "type", "levelParams": [1], "name": 3, "type": 5}},
                {"in": 2, "str": {"pre": 3, "str": "mk"}},
            )
        )
        renumbered = renumber(document)
        assert renumbered is not None
        names = {line["in"]: line["str"]["str"] for line in renumbered.lines if "in" in line}
        quot = next(line["quot"] for line in renumbered.lines if "quot" in line)
        self.assertEqual(names[quot["name"]], "Quot")
        expressions = {line["ie"]: line for line in renumbered.lines if "ie" in line}
        self.assertIn(quot["type"], expressions)


class CanonicalFalseTheoremTests(unittest.TestCase):
    def make(self, *lines: dict[str, object]) -> Document:
        return Document((META, *lines))

    def test_direct_forall_prop_prop(self) -> None:
        document = self.make(
            {"ie": 0, "sort": 0},
            {"ie": 1, "bvar": 0},
            {"ie": 2, "forallE": {"binderInfo": "default", "body": 1, "name": 0, "type": 0}},
            {"thm": {"all": [1], "levelParams": [], "name": 1, "type": 2, "value": 2}},
        )
        self.assertTrue(canonical_false_theorem(document))

    def test_definition_wrapped_goal(self) -> None:
        document = self.make(
            {"in": 1, "str": {"pre": 0, "str": "FalseTy"}},
            {"ie": 0, "sort": 0},
            {"ie": 1, "bvar": 0},
            {"ie": 2, "forallE": {"binderInfo": "default", "body": 1, "name": 0, "type": 0}},
            def_line(1, 0, 2),
            {"ie": 3, "const": {"name": 1, "us": []}},
            {"thm": {"all": [2], "levelParams": [], "name": 2, "type": 3, "value": 2}},
        )
        self.assertTrue(canonical_false_theorem(document))

    def test_empty_prop_inductive_goal(self) -> None:
        document = self.make(
            {"in": 1, "str": {"pre": 0, "str": "False"}},
            {"in": 2, "str": {"pre": 0, "str": "boom"}},
            {"ie": 0, "sort": 0},
            {
                "inductive": {
                    "types": [
                        {
                            "all": [1],
                            "ctors": [],
                            "levelParams": [],
                            "name": 1,
                            "numIndices": 0,
                            "numNested": 0,
                            "numParams": 0,
                            "type": 0,
                        }
                    ],
                    "ctors": [],
                    "recs": [],
                }
            },
            {"ie": 1, "const": {"name": 1, "us": []}},
            {"thm": {"all": [2], "levelParams": [], "name": 2, "type": 1, "value": 1}},
        )
        self.assertTrue(canonical_false_theorem(document))

    def test_rejects_axioms_and_unsafe_declarations(self) -> None:
        goal = (
            {"ie": 0, "sort": 0},
            {"ie": 1, "bvar": 0},
            {"ie": 2, "forallE": {"binderInfo": "default", "body": 1, "name": 0, "type": 0}},
        )
        with_axiom = self.make(
            {"in": 1, "str": {"pre": 0, "str": "oops"}},
            *goal,
            {"axiom": {"all": [1], "levelParams": [], "name": 1, "type": 2}},
            {"thm": {"all": [2], "levelParams": [], "name": 2, "type": 2, "value": 2}},
        )
        self.assertFalse(canonical_false_theorem(with_axiom))
        unsafe = self.make(
            {"ie": 0, "sort": 0},
            {"ie": 1, "bvar": 0},
            {
                "def": {
                    "all": [1],
                    "levelParams": [],
                    "name": 1,
                    "safety": "unsafe",
                    "type": 0,
                    "value": 1,
                }
            },
            *goal,
            {"thm": {"all": [2], "levelParams": [], "name": 2, "type": 2, "value": 2}},
        )
        self.assertFalse(canonical_false_theorem(unsafe))

    def test_rejects_ordinary_goals(self) -> None:
        document = self.make(
            {"ie": 0, "sort": 0},
            {"ie": 1, "bvar": 0},
            {"ie": 2, "lam": {"binderInfo": "default", "body": 1, "name": 0, "type": 0}},
            def_line(1, 0, 2),
        )
        self.assertFalse(canonical_false_theorem(document))



class PreludeLinesTests(unittest.TestCase):
    def test_trusted_constants_and_their_dependencies_are_frozen(self) -> None:
        path = Path(__file__).resolve().parents[1] / "corpus/real/slice-s1.ndjson"
        document = Document.load(path)
        lines = list(document.lines)
        names = _name_strings(lines)
        protected = prelude_lines(document)
        state = {
            names[name]: line_no in protected
            for line_no, line in enumerate(lines)
            for name in _declared(line)
        }
        # Nat.add is trusted by name; it is defined through Nat.brecOn.
        self.assertTrue(state["Nat.add"])
        self.assertTrue(state["Nat.brecOn"])
        self.assertTrue(state["Nat.rec"])
        # User-level instances and theorems stay mutable.
        self.assertFalse(state["instAddNat"])
        self.assertFalse(state["proofIrr"])

if __name__ == "__main__":
    unittest.main()
