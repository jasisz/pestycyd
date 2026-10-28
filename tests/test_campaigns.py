import unittest

from pestycyd.campaigns import CAMPAIGNS
from pestycyd.ndjson import Document, Edit, Mutation


class CampaignTests(unittest.TestCase):
    def test_closedness_is_guaranteed_reject(self) -> None:
        document = Document(
            (
                {"meta": {}},
                {"ie": 0, "sort": 0},
                {"ie": 1, "bvar": 0},
                {
                    "def": {
                        "all": [1],
                        "hints": "opaque",
                        "levelParams": [],
                        "name": 1,
                        "safety": "safe",
                        "type": 0,
                        "value": 0,
                    }
                },
            )
        )
        mutations = list(CAMPAIGNS["closedness"].generate(document))
        self.assertEqual({mutation.label for mutation in mutations}, {"def-type-loose", "def-value-loose"})
        self.assertTrue(all(mutation.oracle == "guaranteed-reject" for mutation in mutations))

    def test_boundary_campaign_reaches_u64_max(self) -> None:
        document = Document(({"ie": 0, "bvar": 3},))
        mutations = list(CAMPAIGNS["metadata-boundaries"].generate(document))
        self.assertTrue(any(mutation.value == 2**64 - 1 for mutation in mutations))

    def test_arena_candidate_campaigns_are_ported_as_differential(self) -> None:
        names = ("expression-structure", "declaration-structure", "inductive-structure")
        self.assertTrue(all(name in CAMPAIGNS for name in names))
        self.assertTrue(all(CAMPAIGNS[name].oracle == "differential" for name in names))

    def test_expression_mutation_truncates_after_affected_declaration(self) -> None:
        document = Document(
            (
                {"ie": 0, "bvar": 0},
                {"ie": 1, "lam": {"type": 0, "body": 0}},
                {"def": {"name": 1, "levelParams": [], "type": 1, "value": 1, "safety": "safe"}},
                {"ie": 2, "sort": 0},
            )
        )
        mutation = next(iter(CAMPAIGNS["expression-structure"].generate(document)))
        changed = document.mutated(mutation)
        self.assertEqual(mutation.end_line, 2)
        self.assertEqual(len(changed.lines), 3)

    def test_full_expression_mutation_preserves_downstream_declarations(self) -> None:
        document = Document(
            (
                {"ie": 0, "bvar": 0},
                {"ie": 1, "lam": {"type": 0, "body": 0}},
                {"def": {"name": 1, "levelParams": [], "type": 1, "value": 1, "safety": "safe"}},
                {"ie": 2, "sort": 0},
            )
        )
        mutation = next(iter(CAMPAIGNS["expression-structure-full"].generate(document)))
        changed = document.mutated(mutation)
        self.assertIsNone(mutation.end_line)
        self.assertEqual(len(changed.lines), len(document.lines))

    def test_scope_compatible_splicing_uses_only_prior_nodes_that_fit_scope(self) -> None:
        document = Document(
            (
                {"ie": 0, "sort": 0},
                {"ie": 1, "bvar": 0},
                {"ie": 2, "lam": {"type": 0, "body": 1}},
                {"ie": 3, "const": {"name": 1, "us": []}},
                {"ie": 4, "app": {"fn": 3, "arg": 0}},
                {"ie": 5, "bvar": 1},
            )
        )
        mutations = list(CAMPAIGNS["scope-compatible-splicing"].generate(document))
        app_mutations = [mutation for mutation in mutations if mutation.line == 4]
        self.assertTrue(any(mutation.value == 2 for mutation in app_mutations))
        self.assertFalse(any(mutation.value == 5 for mutation in app_mutations))
        self.assertTrue(all(mutation.end_line is None for mutation in mutations))

    def test_goal_value_splicing_only_mutates_final_theorem_value_dag(self) -> None:
        document = Document(
            (
                {"ie": 0, "sort": 0},
                {"ie": 1, "const": {"name": 1, "us": []}},
                {"ie": 2, "app": {"fn": 1, "arg": 0}},
                {"ie": 3, "app": {"fn": 1, "arg": 2}},
                {"thm": {"name": 2, "levelParams": [], "type": 0, "value": 3}},
            )
        )
        mutations = list(CAMPAIGNS["goal-value-splicing"].generate(document))
        self.assertTrue(mutations)
        self.assertEqual({mutation.line for mutation in mutations}, {2, 3})
        self.assertTrue(all(mutation.label.startswith("goal-") for mutation in mutations))

    def test_recursor_rule_constant_splicing_targets_rule_dag_and_level_arity(self) -> None:
        document = Document(
            (
                {"ie": 0, "const": {"name": 10, "us": [1]}},
                {"ie": 1, "const": {"name": 11, "us": []}},
                {"ie": 2, "const": {"name": 12, "us": [1]}},
                {"ie": 3, "app": {"fn": 2, "arg": 1}},
                {
                    "inductive": {
                        "types": [],
                        "ctors": [],
                        "recs": [{"rules": [{"rhs": 3}]}],
                    }
                },
                {"ie": 4, "const": {"name": 13, "us": [1]}},
            )
        )
        mutations = list(CAMPAIGNS["recursor-rule-constant-splicing"].generate(document))
        self.assertEqual(len(mutations), 1)
        self.assertEqual(mutations[0].line, 2)
        self.assertEqual(mutations[0].value, 10)
        self.assertTrue(mutations[0].label.startswith("rule-"))

    def test_universe_structure_preserves_level_id_and_backward_references(self) -> None:
        document = Document(
            (
                {"il": 1, "succ": 0},
                {"il": 2, "max": [0, 1]},
                {"il": 3, "imax": [1, 2]},
            )
        )
        mutations = list(CAMPAIGNS["universe-structure"].generate(document))
        switch = next(mutation for mutation in mutations if mutation.label == "imax-to-max")
        changed = document.mutated(switch)
        self.assertEqual(changed.lines[2], {"il": 3, "max": [1, 2]})
        for mutation in mutations:
            changed_line = document.mutated(mutation).lines[mutation.line]
            self.assertEqual(changed_line["il"], document.lines[mutation.line]["il"])
            refs = changed_line.get("succ") or changed_line.get("max") or changed_line.get("imax")
            values = refs if isinstance(refs, list) else [refs]
            self.assertTrue(all(value is None or value < changed_line["il"] for value in values))

    def test_full_inductive_mutation_preserves_final_theorem(self) -> None:
        document = Document(
            (
                {
                    "inductive": {
                        "types": [
                            {
                                "name": 1,
                                "levelParams": [],
                                "type": 0,
                                "numParams": 0,
                                "numIndices": 0,
                                "numNested": 0,
                                "ctors": [],
                                "isRec": False,
                                "isReflexive": False,
                                "isUnsafe": False,
                            }
                        ],
                        "ctors": [],
                        "recs": [],
                    }
                },
                {"thm": {"name": 2, "levelParams": [], "type": 0, "value": 0}},
            )
        )
        mutation = next(iter(CAMPAIGNS["inductive-structure-full"].generate(document)))
        changed = document.mutated(mutation)
        self.assertIsNone(mutation.end_line)
        self.assertEqual(len(changed.lines), 2)
        self.assertIn("thm", changed.lines[-1])

    def test_inductive_structure_swaps_constructor_order_atomically(self) -> None:
        document = Document(
            (
                {
                    "inductive": {
                        "types": [{"name": 1, "ctors": [2, 3]}],
                        "ctors": [],
                        "recs": [],
                    }
                },
            )
        )
        mutation = next(
            mutation
            for mutation in CAMPAIGNS["inductive-structure"].generate(document)
            if mutation.label == "types-0-ctors-0-1-swap"
        )
        changed = document.mutated(mutation)
        self.assertEqual(changed.lines[0]["inductive"]["types"][0]["ctors"], [3, 2])
        self.assertEqual(mutation.target, "constructor membership and ordering")

    def test_inductive_structure_omits_recursor_entry_atomically(self) -> None:
        document = Document(
            (
                {
                    "inductive": {
                        "types": [],
                        "ctors": [],
                        "recs": [{"name": 1}, {"name": 2}],
                    }
                },
            )
        )
        mutation = next(
            mutation
            for mutation in CAMPAIGNS["inductive-structure"].generate(document)
            if mutation.label == "recs-0-omit"
        )
        changed = document.mutated(mutation)
        self.assertEqual(changed.lines[0]["inductive"]["recs"], [{"name": 2}])
        self.assertEqual(mutation.target, "inductive recs membership completeness")

    def test_compound_mutation_applies_all_edits_atomically(self) -> None:
        document = Document(({"left": {"x": 1}, "right": {"x": 2}},))
        mutation = Mutation(
            "test", "swap", "differential", 0, ("left",), "x", 2, "test",
            edits=(Edit(0, ("right",), "x", 1),),
        )
        changed = document.mutated(mutation)
        self.assertEqual(changed.lines[0]["left"]["x"], 2)
        self.assertEqual(changed.lines[0]["right"]["x"], 1)

    def test_field_deletion_removes_mandatory_recursor_rule_field(self) -> None:
        document = Document(
            (
                {
                    "inductive": {
                        "types": [],
                        "ctors": [],
                        "recs": [
                            {
                                "name": 1,
                                "levelParams": [],
                                "type": 0,
                                "numParams": 0,
                                "numIndices": 0,
                                "numMotives": 1,
                                "numMinors": 1,
                                "rules": [{"ctor": 2, "nfields": 0, "rhs": 3}],
                                "k": False,
                                "isUnsafe": False,
                            }
                        ],
                    }
                },
            )
        )
        mutation = next(
            mutation
            for mutation in CAMPAIGNS["field-deletion"].generate(document)
            if mutation.label == "delete-recs-0-rule-0-rhs"
        )
        changed = document.mutated(mutation)
        self.assertNotIn("rhs", changed.lines[0]["inductive"]["recs"][0]["rules"][0])
        self.assertTrue(mutation.delete)

    def test_declaration_replay_duplicates_a_shadowable_copy(self) -> None:
        declaration = {
            "def": {
                "name": 1,
                "levelParams": [],
                "type": 0,
                "value": 0,
                "safety": "safe",
            }
        }
        document = Document(
            (
                {"ie": 0, "sort": 0},
                declaration,
                {"thm": {"name": 2, "levelParams": [], "type": 0, "value": 0}},
            )
        )
        mutation = next(
            mutation
            for mutation in CAMPAIGNS["declaration-replay"].generate(document)
            if mutation.label.startswith("duplicate-def")
        )
        changed = document.mutated(mutation)
        self.assertEqual(len(changed.lines), 4)
        self.assertEqual(changed.lines[1], changed.lines[2])
        self.assertEqual(changed.final_goal_lines(), frozenset({0, 3}))
        self.assertEqual(mutation.line_edits[0].kind, "insert")

    def test_declaration_shadow_copy_corrupts_only_inserted_copy(self) -> None:
        declaration = {
            "def": {
                "name": 1,
                "levelParams": [],
                "type": 10,
                "value": 20,
                "safety": "safe",
            }
        }
        document = Document((declaration,))
        mutation = next(
            mutation
            for mutation in CAMPAIGNS["declaration-shadow-copy"].generate(document)
            if mutation.label == "shadow-def-type-from-value"
        )
        changed = document.mutated(mutation)
        self.assertEqual(changed.lines[0]["def"]["type"], 10)
        self.assertEqual(changed.lines[1]["def"]["type"], 20)
        self.assertEqual(changed.lines[0]["def"]["name"], changed.lines[1]["def"]["name"])

    def test_final_goal_protection_follows_expression_dependencies(self) -> None:
        document = Document(
            (
                {"ie": 0, "sort": 0},
                {"ie": 1, "const": {"name": 1, "us": []}},
                {"ie": 2, "app": {"fn": 0, "arg": 1}},
                {"ie": 3, "sort": 1},
                {"thm": {"name": 2, "levelParams": [], "type": 2, "value": 1}},
            )
        )
        self.assertEqual(document.final_goal_lines(), frozenset({0, 1, 2, 4}))

    def test_universe_crosswire_can_swap_two_occurrences(self) -> None:
        document = Document(
            (
                {"const": {"name": 1, "us": [2]}, "ie": 0},
                {"const": {"name": 1, "us": [3]}, "ie": 1},
            )
        )
        mutations = list(CAMPAIGNS["const-universe-crosswire"].generate(document))
        swap = next(mutation for mutation in mutations if "swap" in mutation.label)
        changed = document.mutated(swap)
        self.assertEqual(changed.lines[0]["const"]["us"], [3])
        self.assertEqual(changed.lines[1]["const"]["us"], [2])

    def test_typed_neighborhood_swaps_arguments_of_same_function(self) -> None:
        document = Document(
            (
                {"ie": 0, "sort": 0},
                {"ie": 1, "const": {"name": 1, "us": []}},
                {"ie": 2, "const": {"name": 2, "us": []}},
                {"ie": 3, "app": {"fn": 0, "arg": 1}},
                {"ie": 4, "app": {"fn": 0, "arg": 2}},
            )
        )
        mutations = list(CAMPAIGNS["typed-neighborhood-crosswire"].generate(document))
        swap = next(
            mutation
            for mutation in mutations
            if mutation.label.startswith("same-fn-app-arg") and mutation.label.endswith("-swap")
        )
        changed = document.mutated(swap)
        self.assertEqual(changed.lines[3]["app"]["arg"], 2)
        self.assertEqual(changed.lines[4]["app"]["arg"], 1)

    def test_typed_neighborhood_does_not_create_forward_reference(self) -> None:
        document = Document(
            (
                {"ie": 0, "sort": 0},
                {"ie": 1, "const": {"name": 1, "us": []}},
                {"ie": 2, "app": {"fn": 0, "arg": 1}},
                {"ie": 3, "const": {"name": 2, "us": []}},
                {"ie": 4, "app": {"fn": 0, "arg": 3}},
            )
        )
        mutations = list(CAMPAIGNS["typed-neighborhood-crosswire"].generate(document))
        same_function = [
            mutation for mutation in mutations if mutation.label.startswith("same-fn-app-arg")
        ]
        self.assertEqual(len(same_function), 1)
        self.assertTrue(same_function[0].label.endswith("-from-prior"))

    def test_binder_context_campaign_pairs_pi_and_lambda_in_declaration(self) -> None:
        document = Document(
            (
                {"ie": 0, "sort": 0},
                {"ie": 1, "forallE": {"type": 0, "body": 0}},
                {"ie": 2, "lam": {"type": 0, "body": 0}},
                {"def": {"name": 1, "levelParams": [], "type": 0, "value": 0, "safety": "safe"}},
            )
        )
        mutation = next(iter(CAMPAIGNS["binder-context-pairs"].generate(document)))
        changed = document.mutated(mutation)
        self.assertEqual(changed.lines[3]["def"]["type"], 1)
        self.assertEqual(changed.lines[3]["def"]["value"], 2)

    def test_recursor_permutation_swaps_both_rule_rhs_values(self) -> None:
        document = Document(
            (
                {
                    "inductive": {
                        "recs": [
                            {"rules": [{"ctor": 1, "rhs": 10}, {"ctor": 2, "rhs": 20}]}
                        ]
                    }
                },
            )
        )
        mutations = list(CAMPAIGNS["recursor-rule-permutations"].generate(document))
        swap = next(mutation for mutation in mutations if mutation.label.endswith("swap-rhs"))
        changed = document.mutated(swap)
        rules = changed.lines[0]["inductive"]["recs"][0]["rules"]
        self.assertEqual([rule["rhs"] for rule in rules], [20, 10])

    def test_inductive_block_crosswire_maps_rhs_onto_later_constructor(self) -> None:
        def block(type_name: int, ctor_name: int, rec_name: int, rhs: int) -> dict[str, object]:
            return {
                "inductive": {
                    "types": [
                        {
                            "name": type_name,
                            "type": 0,
                            "numParams": 0,
                            "numIndices": 0,
                        }
                    ],
                    "ctors": [
                        {
                            "name": ctor_name,
                            "induct": type_name,
                            "type": 0,
                            "cidx": 0,
                            "numParams": 0,
                            "numFields": 0,
                        }
                    ],
                    "recs": [
                        {
                            "name": rec_name,
                            "type": 0,
                            "numParams": 0,
                            "numIndices": 0,
                            "numMotives": 1,
                            "numMinors": 1,
                            "rules": [{"ctor": ctor_name, "nfields": 0, "rhs": rhs}],
                        }
                    ],
                }
            }

        document = Document((block(1, 2, 3, 10), block(4, 5, 6, 20)))
        mutations = list(CAMPAIGNS["inductive-block-crosswire"].generate(document))
        rhs = next(mutation for mutation in mutations if mutation.label.endswith("rule-0-rhs"))
        changed = document.mutated(rhs)
        rule = changed.lines[1]["inductive"]["recs"][0]["rules"][0]
        self.assertEqual(rule["ctor"], 5)
        self.assertEqual(rule["rhs"], 10)
        self.assertIsNone(rhs.end_line)

    def test_inductive_block_crosswire_never_references_later_block(self) -> None:
        document = Document(
            (
                {
                    "inductive": {
                        "types": [],
                        "ctors": [],
                        "recs": [
                            {
                                "type": 1,
                                "numParams": 0,
                                "numIndices": 0,
                                "numMotives": 1,
                                "numMinors": 1,
                                "rules": [{"ctor": 1, "nfields": 0, "rhs": 10}],
                            }
                        ],
                    }
                },
                {
                    "inductive": {
                        "types": [],
                        "ctors": [],
                        "recs": [
                            {
                                "type": 2,
                                "numParams": 0,
                                "numIndices": 0,
                                "numMotives": 1,
                                "numMinors": 1,
                                "rules": [{"ctor": 2, "nfields": 0, "rhs": 20}],
                            }
                        ],
                    }
                },
            )
        )
        mutations = list(CAMPAIGNS["inductive-block-crosswire"].generate(document))
        self.assertTrue(mutations)
        self.assertTrue(all(mutation.line == 1 and mutation.value != 20 for mutation in mutations))

    def test_inductive_block_crosswire_can_cross_different_recursor_counts(self) -> None:
        document = Document(
            (
                {"ie": 10, "sort": 0},
                {"ie": 20, "sort": 0},
                {
                    "inductive": {
                        "types": [],
                        "ctors": [],
                        "recs": [
                            {
                                "numParams": 2,
                                "numIndices": 1,
                                "numMotives": 1,
                                "numMinors": 1,
                                "rules": [{"ctor": 1, "nfields": 0, "rhs": 10}],
                            }
                        ],
                    }
                },
                {
                    "inductive": {
                        "types": [],
                        "ctors": [],
                        "recs": [
                            {
                                "numParams": 0,
                                "numIndices": 0,
                                "numMotives": 1,
                                "numMinors": 1,
                                "rules": [{"ctor": 2, "nfields": 0, "rhs": 20}],
                            }
                        ],
                    }
                },
            )
        )
        mutation = next(
            mutation
            for mutation in CAMPAIGNS["inductive-block-crosswire"].generate(document)
            if "into-rec" in mutation.label
        )
        changed = document.mutated(mutation)
        rule = changed.lines[3]["inductive"]["recs"][0]["rules"][0]
        self.assertEqual(rule, {"ctor": 2, "nfields": 0, "rhs": 10})

    def test_intern_table_shadowing_keeps_original_and_inserts_duplicate(self) -> None:
        document = Document(
            (
                {"ie": 0, "sort": 0},
                {"ie": 1, "sort": 1},
                {"ie": 2, "app": {"fn": 0, "arg": 1}},
                {
                    "def": {
                        "name": 1,
                        "levelParams": [],
                        "type": 0,
                        "value": 2,
                        "safety": "safe",
                    }
                },
            )
        )
        mutation = next(
            mutation
            for mutation in CAMPAIGNS["intern-table-shadowing"].generate(document)
            if mutation.label.startswith("ie-0-from-line-2")
        )
        changed = document.mutated(mutation)
        self.assertEqual(changed.lines[0], {"ie": 0, "sort": 0})
        self.assertEqual(changed.lines[3], {"ie": 0, "sort": 1})
        self.assertIn("def", changed.lines[4])
        self.assertEqual(len(changed.lines), len(document.lines) + 1)

    def test_guaranteed_level_oracle_skips_unsafe_declarations(self) -> None:
        document = Document(
            (
                {
                    "def": {
                        "name": 1,
                        "levelParams": [2],
                        "type": 0,
                        "value": 0,
                        "safety": "unsafe",
                    }
                },
            )
        )
        self.assertEqual(list(CAMPAIGNS["level-params"].generate(document)), [])


if __name__ == "__main__":
    unittest.main()

