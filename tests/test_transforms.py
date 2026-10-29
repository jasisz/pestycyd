import unittest

from pestycyd.campaigns import CAMPAIGNS
from pestycyd.cli import _compose_lineage_oracle
from pestycyd.minimize import well_formed_export
from pestycyd.ndjson import Document
from pestycyd.transforms import (
    NONZERO_IMPOSTORS,
    ZERO_DISGUISES,
    append_prop_impostor,
    clonable_value,
    swap_independent_declarations,
    wrap_beta,
    wrap_let,
)


META = {"meta": {"format": {"version": "3.1.0"}}}


def expr_table(document: Document) -> dict[int, dict[str, object]]:
    return {
        line["ie"]: line
        for line in document.lines
        if isinstance(line.get("ie"), int) and not isinstance(line.get("ie"), bool)
    }


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


class TransformTests(unittest.TestCase):
    def setUp(self) -> None:
        self.document = Document(
            (
                META,
                {"in": 1, "str": {"pre": 0, "str": "A"}},
                {"ie": 0, "sort": 0},
                {"ie": 1, "bvar": 0},
                {"ie": 2, "lam": {"binderInfo": "default", "body": 1, "name": 1, "type": 0}},
                def_line(1, 0, 2),
            )
        )

    def assert_well_formed(self, document: Document) -> None:
        self.assertTrue(well_formed_export(document.render().splitlines()))

    def test_prop_disguise_moves_one_reference_to_a_fresh_sort(self) -> None:
        mutations = list(CAMPAIGNS["prop-disguise"].generate(self.document))
        self.assertEqual([m.value for m in mutations], list(ZERO_DISGUISES))
        nested = next(m for m in mutations if m.value == "imax-1-imax-1-0")
        changed = self.document.mutated(nested)
        self.assert_well_formed(changed)
        levels = {line["il"]: line for line in changed.lines if "il" in line}
        table = expr_table(changed)
        declaration = next(line["def"] for line in changed.lines if "def" in line)
        self.assertEqual(levels[table[declaration["type"]]["sort"]], {"il": 3, "imax": [1, 2]})
        self.assertEqual(levels[2], {"il": 2, "imax": [1, 0]})
        # The shared Sort 0 node still serves the lambda binder.
        lam = next(line for line in changed.lines if "lam" in line)
        self.assertEqual(table[lam["lam"]["type"]], {"ie": 0, "sort": 0})

    def test_prop_impostor_appends_a_valid_type_and_an_invalid_theorem(self) -> None:
        from pathlib import Path

        seed = Document.load(Path(__file__).resolve().parents[1] / "corpus/real/slice-s1.ndjson")
        mutations = list(CAMPAIGNS["prop-impostor"].generate(seed))
        self.assertEqual([m.value for m in mutations], list(NONZERO_IMPOSTORS))
        self.assertTrue(all(m.oracle == "guaranteed-reject" for m in mutations))
        changed = seed.mutated(mutations[0])
        self.assert_well_formed(changed)
        self.assertIn("thm", changed.lines[-1])
        control = append_prop_impostor(seed, "imax-0-1", with_theorem=False)
        self.assert_well_formed(control)
        self.assertIn("def", control.lines[-1])
        self.assertEqual(list(CAMPAIGNS["prop-impostor"].generate(self.document)), [])

    def test_wrap_eta_builds_expanded_lambda(self) -> None:
        document = Document(
            (
                META,
                {"in": 1, "str": {"pre": 0, "str": "id"}},
                {"ie": 0, "sort": 0},
                {"ie": 1, "bvar": 0},
                {"ie": 2, "forallE": {"binderInfo": "default", "body": 1, "name": 0, "type": 0}},
                def_line(1, 2, 1),
            )
        )
        mutations = list(CAMPAIGNS["metamorphic-eta"].generate(document))
        self.assertEqual(len(mutations), 1)
        changed = document.mutated(mutations[0])
        self.assert_well_formed(changed)
        table = expr_table(changed)
        declaration = changed.lines[-1]["def"]
        lam = table[declaration["value"]]["lam"]
        self.assertEqual(lam["type"], 0)  # domain of the declaration's Pi
        application = table[lam["body"]]["app"]
        self.assertEqual(application["fn"], 1)  # the original value
        self.assertEqual(table[application["arg"]]["bvar"], 0)

    def test_wrap_eta_skips_non_pi_types(self) -> None:
        document = Document(
            (
                META,
                {"in": 1, "str": {"pre": 0, "str": "A"}},
                {"ie": 0, "sort": 0},
                {"ie": 1, "bvar": 0},
                def_line(1, 0, 1),  # type is a sort, not a Pi
            )
        )
        self.assertEqual(list(CAMPAIGNS["metamorphic-eta"].generate(document)), [])

    def test_wrap_beta_builds_identity_application(self) -> None:
        changed = wrap_beta(self.document, 5, ("def",))
        self.assert_well_formed(changed)
        table = expr_table(changed)
        declaration = changed.lines[-1]["def"]
        app = table[declaration["value"]]["app"]
        lam = table[app["fn"]]["lam"]
        self.assertEqual(table[lam["body"]]["bvar"], 0)
        self.assertEqual(lam["type"], declaration["type"])
        self.assertEqual(app["arg"], 2)
        # The original records survive untouched before the inserted fragment.
        self.assertEqual(changed.lines[3], {"ie": 1, "bvar": 0})

    def test_wrap_let_builds_redundant_binding(self) -> None:
        changed = wrap_let(self.document, 5, ("def",))
        self.assert_well_formed(changed)
        table = expr_table(changed)
        declaration = changed.lines[-1]["def"]
        let = table[declaration["value"]]["letE"]
        self.assertEqual(let["value"], 2)
        self.assertEqual(let["type"], declaration["type"])
        self.assertEqual(table[let["body"]]["bvar"], 0)
        self.assertIn("nondep", let)

    def test_rename_declaration_remaps_references(self) -> None:
        document = Document(
            (
                META,
                {"in": 1, "str": {"pre": 0, "str": "A"}},
                {"in": 2, "str": {"pre": 0, "str": "user"}},
                {"ie": 0, "sort": 0},
                {"ie": 1, "const": {"name": 1, "us": []}},
                def_line(1, 0, 1),
                {
                    "thm": {
                        "all": [2, 1],
                        "levelParams": [],
                        "name": 2,
                        "type": 0,
                        "value": 1,
                    }
                },
            )
        )
        mutation = next(
            m
            for m in CAMPAIGNS["metamorphic-rename"].generate(document)
            if m.path == ("def",)
        )
        changed = document.mutated(mutation)
        self.assert_well_formed(changed)
        fresh = next(
            line["in"]
            for line in changed.lines
            if isinstance(line.get("str"), dict) and line["str"]["str"] == "pyd1"
        )
        # The fresh record sits right after the old name's record, so the
        # later "user" name shifted by one.
        self.assertEqual(fresh, 2)
        definition = changed.lines[6]["def"]
        self.assertEqual(definition["name"], fresh)
        self.assertEqual(definition["all"], [fresh])
        # A constant occurrence of the renamed declaration follows the rename.
        self.assertEqual(changed.lines[5]["const"]["name"], fresh)
        theorem = changed.lines[-1]["thm"]
        self.assertEqual(theorem["name"], 3)
        self.assertEqual(theorem["all"], [3, fresh])

    def test_rename_refuses_shared_names(self) -> None:
        document = Document(
            (
                META,
                {"in": 1, "str": {"pre": 0, "str": "A"}},
                {"ie": 0, "sort": 0},
                def_line(1, 0, 0),
                def_line(1, 0, 0),  # same interned name, second declaration
            )
        )
        self.assertEqual(list(CAMPAIGNS["metamorphic-rename"].generate(document)), [])

    def test_clone_value_dag_unshares_shared_subterms(self) -> None:
        document = Document(
            (
                META,
                {"in": 1, "str": {"pre": 0, "str": "A"}},
                {"in": 2, "str": {"pre": 0, "str": "B"}},
                {"ie": 0, "sort": 0},
                {"ie": 1, "bvar": 0},
                {"ie": 2, "bvar": 7},
                {"ie": 3, "lam": {"binderInfo": "default", "body": 1, "name": 1, "type": 0}},
                {"ie": 4, "app": {"arg": 3, "fn": 3}},
                def_line(1, 0, 3),
                def_line(2, 0, 4),
            )
        )
        self.assertTrue(clonable_value(document, 8, ("def",)))
        changed = document.mutated(
            next(CAMPAIGNS["expression-unsharing"].generate(document))
        )
        self.assert_well_formed(changed)
        table = expr_table(changed)
        cloned = changed.lines[-2]["def"]
        other = changed.lines[-1]["def"]
        # The mutation target now points at a private, structurally
        # identical copy of the lambda...
        clone_root = cloned["value"]
        self.assertNotEqual(clone_root, 3)
        clone = table[clone_root]
        self.assertIn("lam", clone)
        self.assertEqual(table[clone["lam"]["body"]]["bvar"], 0)
        # ...while the other declaration's application still uses the
        # original shared node.
        self.assertEqual(other["value"], 4)
        self.assertEqual(table[other["value"]]["app"]["arg"], 3)

    def test_clone_skips_unshared_values(self) -> None:
        document = Document(
            (
                META,
                {"in": 1, "str": {"pre": 0, "str": "A"}},
                {"ie": 0, "sort": 0},
                {"ie": 1, "bvar": 0},
                {"ie": 2, "lam": {"binderInfo": "default", "body": 1, "name": 1, "type": 0}},
                def_line(1, 0, 2),
            )
        )
        self.assertFalse(clonable_value(document, 5, ("def",)))
        self.assertEqual(list(CAMPAIGNS["expression-unsharing"].generate(document)), [])

    def test_reordering_moves_declaration_after_next(self) -> None:
        document = Document(
            (
                META,
                {"in": 1, "str": {"pre": 0, "str": "A"}},
                {"in": 2, "str": {"pre": 0, "str": "B"}},
                {"ie": 0, "sort": 0},
                {"ie": 1, "bvar": 0},
                def_line(1, 0, 0),
                def_line(2, 0, 1),
            )
        )
        self.assertTrue(swap_independent_declarations(document, 5))
        changed = document.mutated(
            next(CAMPAIGNS["declaration-reordering"].generate(document))
        )
        self.assert_well_formed(changed)
        self.assertEqual(changed.lines[5]["def"]["name"], 2)
        self.assertEqual(changed.lines[6]["def"]["name"], 1)

    def test_reordering_guard_rejects_dependencies(self) -> None:
        document = Document(
            (
                META,
                {"in": 1, "str": {"pre": 0, "str": "A"}},
                {"in": 2, "str": {"pre": 0, "str": "B"}},
                {"ie": 0, "sort": 0},
                {"ie": 1, "bvar": 0},
                {"ie": 2, "const": {"name": 1, "us": []}},
                def_line(1, 0, 0),
                def_line(2, 0, 2),  # references constant A
            )
        )
        self.assertFalse(swap_independent_declarations(document, 6))
        self.assertEqual(
            [m for m in CAMPAIGNS["declaration-reordering"].generate(document) if m.line == 6],
            [],
        )

    def test_reordering_never_crosses_an_inductive(self) -> None:
        """Kernel-derived names make such swaps order-sensitive.

        Processing an inductive checks ``<ind>.rec`` and generates
        ``_nested.*`` against the environment as it goes, and the
        official kernel rejects a taken recursor name — so moving a plain
        declaration across a block is not validity-preserving even when
        the two reference none of each other's names.
        """
        document = Document(
            (
                META,
                {"in": 1, "str": {"pre": 0, "str": "helper"}},
                {"in": 2, "str": {"pre": 0, "str": "Box"}},
                {"ie": 0, "sort": 0},
                {"ie": 1, "bvar": 0},
                def_line(1, 0, 1),
                {
                    "inductive": {
                        "types": [
                            {
                                "all": [2],
                                "ctors": [],
                                "levelParams": [],
                                "name": 2,
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
            )
        )
        self.assertFalse(swap_independent_declarations(document, 5))
        self.assertEqual(
            list(CAMPAIGNS["declaration-reordering"].generate(document)), []
        )

    def test_reordering_refuses_recursor_shaped_names(self) -> None:
        document = Document(
            (
                META,
                {"in": 1, "str": {"pre": 0, "str": "Box"}},
                {"in": 2, "str": {"pre": 1, "str": "rec"}},
                {"in": 3, "str": {"pre": 0, "str": "later"}},
                {"ie": 0, "sort": 0},
                {"ie": 1, "bvar": 0},
                def_line(2, 0, 1),
                def_line(3, 0, 1),
            )
        )
        self.assertFalse(swap_independent_declarations(document, 6))
        self.assertEqual(
            [m for m in CAMPAIGNS["declaration-reordering"].generate(document) if m.line == 6],
            [],
        )

    def test_rename_skips_trusted_primitive_names(self) -> None:
        """Checkers key native reduction on names like Nat.add.

        Renaming such a declaration removes it from the trust mechanism,
        so the rewrite changes meaning instead of presentation and the
        guaranteed-accept oracle must not fire.
        """
        document = Document(
            (
                META,
                {"in": 1, "str": {"pre": 0, "str": "Nat"}},
                {"in": 2, "str": {"pre": 1, "str": "add"}},
                {"ie": 0, "sort": 0},
                {"ie": 1, "bvar": 0},
                def_line(2, 0, 1),
            )
        )
        self.assertEqual(list(CAMPAIGNS["metamorphic-rename"].generate(document)), [])
        plain = Document(
            (
                META,
                {"in": 1, "str": {"pre": 0, "str": "ordinary"}},
                {"ie": 0, "sort": 0},
                {"ie": 1, "bvar": 0},
                def_line(1, 0, 1),
            )
        )
        self.assertTrue(list(CAMPAIGNS["metamorphic-rename"].generate(plain)))

    def test_all_metamorphic_campaigns_are_guaranteed_accept(self) -> None:
        for name in (
            "metamorphic-beta",
            "metamorphic-let",
            "metamorphic-rename",
            "expression-unsharing",
            "declaration-reordering",
        ):
            self.assertEqual(CAMPAIGNS[name].oracle, "guaranteed-accept")

    def test_guaranteed_accept_oracle_composes_through_lineage(self) -> None:
        self.assertEqual(
            _compose_lineage_oracle("guaranteed-accept", "guaranteed-accept"),
            "guaranteed-accept",
        )
        self.assertEqual(
            _compose_lineage_oracle("guaranteed-accept", "differential"),
            "differential",
        )
        self.assertEqual(
            _compose_lineage_oracle("differential", "guaranteed-accept"),
            "differential",
        )

    def test_wrappers_skip_unsafe_declarations(self) -> None:
        document = Document(
            (
                META,
                {"ie": 0, "sort": 0},
                {
                    "def": {
                        "all": [1],
                        "levelParams": [],
                        "name": 1,
                        "safety": "unsafe",
                        "type": 0,
                        "value": 0,
                    }
                },
            )
        )
        self.assertEqual(list(CAMPAIGNS["metamorphic-beta"].generate(document)), [])
        self.assertEqual(list(CAMPAIGNS["metamorphic-let"].generate(document)), [])


if __name__ == "__main__":
    unittest.main()
