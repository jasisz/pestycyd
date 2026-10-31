import tempfile
import unittest
from pathlib import Path

from pestycyd.triage import load_rules, load_triage, mutation_sites, triage

RULES = """
[[rule]]
id = "derived-rules"
why = "derives recursor rules"
kernels = ["con-*"]
status = ["accept"]
expected = ["reject"]
sites = ["inductive.recs.rules*"]

[[rule]]
id = "budget"
kernels = ["kefir"]
status = "decline"
output = '"code":"resource\\.'
"""


def result(status: str, output: str = "") -> dict[str, object]:
    return {"status": status, "output": output}


class TriageTests(unittest.TestCase):
    def setUp(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "triage.toml"
            path.write_text(RULES)
            self.rules = load_rules(path)

    def test_every_deviation_explained_makes_a_known_finding(self) -> None:
        verdict = triage(
            self.rules,
            "recursor-crosswire",
            "swap",
            "differential",
            {
                "official": result("reject"),
                "con-leche": result("accept"),
                "con-ron": result("accept"),
                "kefir": result("decline", '{"code":"resource.reduction_path"}'),
            },
            frozenset({"inductive.recs.rules.rhs"}),
        )
        self.assertEqual(verdict.expected, "reject")
        self.assertTrue(verdict.known)
        self.assertEqual(verdict.rule_ids, ("budget", "derived-rules"))

    def test_a_known_reference_bug_overturns_the_expected_verdict(self) -> None:
        results = {
            "official": result("reject", "(kernel) unknown constant 'Bool'"),
            "lean4lean": result("reject", "at T: (kernel) unknown constant 'Bool'"),
            "nanoda": result("accept"),
            "pestka-old": result("accept"),
        }
        verdict = triage(load_triage(), "namespace-shuffle", "roots-2-variant-0", "differential", results)
        self.assertEqual(verdict.expected, "accept")
        self.assertTrue(verdict.known)
        self.assertEqual(verdict.rule_ids, ("lean4-16133-replay-mutual-order",))

    def test_a_deviation_outside_the_rule_sites_stays_unexplained(self) -> None:
        verdict = triage(
            self.rules,
            "expression-structure",
            "lam-body",
            "differential",
            {"official": result("reject"), "con-leche": result("accept")},
            frozenset({"inductive.recs.rules.rhs", "def.value"}),
        )
        self.assertFalse(verdict.known)
        self.assertEqual(verdict.unexplained, ("con-leche",))

    def test_oracle_sets_the_expected_verdict(self) -> None:
        verdict = triage(
            self.rules,
            "literal-arith",
            "Nat.gcd",
            "guaranteed-accept",
            {"official": result("reject"), "kefir": result("decline", '"code":"support.x"')},
        )
        self.assertEqual(verdict.expected, "accept")
        self.assertEqual(verdict.unexplained, ("kefir", "official"))

    def test_sites_follow_table_records_to_declaration_fields(self) -> None:
        lines = [
            {"meta": {}},
            {"ie": 0, "sort": 0},
            {"ie": 1, "lam": {"binderInfo": "default", "name": 0, "type": 0, "body": 0}},
            {"inductive": {"types": [], "ctors": [], "recs": [{"type": 0, "rules": [{"rhs": 1}]}]}},
        ]
        rhs_only = {"line": 2, "path": ["lam"], "field": "body"}
        self.assertEqual(mutation_sites(lines, rhs_only), frozenset({"inductive.recs.rules.rhs"}))
        shared = {"line": 1, "path": [], "field": "sort"}
        self.assertEqual(
            mutation_sites(lines, shared),
            frozenset({"inductive.recs.rules.rhs", "inductive.recs.type"}),
        )
        direct = {"line": 3, "path": ["inductive", "recs", 0, "rules", 0], "field": "rhs"}
        self.assertEqual(mutation_sites(lines, direct), frozenset({"inductive.recs.rules.rhs"}))

    def test_builtin_rules_load(self) -> None:
        ids = [rule.id for rule in load_triage()]
        self.assertIn("kefir-resource-budget", ids)
        self.assertEqual(len(ids), len(set(ids)))

    def test_unknown_rule_keys_are_refused(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "triage.toml"
            path.write_text('[[rule]]\nid = "x"\nkernels = ["a"]\nstatus = ["accept"]\nkernel = "typo"\n')
            with self.assertRaises(ValueError):
                load_rules(path)


if __name__ == "__main__":
    unittest.main()
