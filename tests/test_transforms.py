import unittest

from pestycyd.campaigns import CAMPAIGNS
from pestycyd.cli import _compose_lineage_oracle
from pestycyd.minimize import well_formed_export
from pestycyd.ndjson import Document
from pestycyd.transforms import (
    FIELD_FAULTS,
    NONZERO_IMPOSTORS,
    SAFETY_FAULTS,
    UNDECLARED_INDUCTIVE_SITES,
    ZERO_DISGUISES,
    append_field_inductive,
    append_prop_impostor,
    append_index_elimination,
    append_safety_fault,
    append_undeclared_inductive,
    clonable_value,
    rename_safe,
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

    def test_single_fault_breaks_one_rule_and_stays_well_formed(self) -> None:
        # A = fun (x : Prop) => x : Prop -> Prop, plus T : Type := Prop.
        document = Document(
            (
                *self.document.lines[:-1],
                {"ie": 3, "forallE": {"binderInfo": "default", "body": 0, "name": 1, "type": 0}},
                def_line(1, 3, 2),
                {"in": 2, "str": {"pre": 0, "str": "T"}},
                {"il": 1, "succ": 0},
                {"ie": 4, "sort": 1},
                def_line(2, 4, 0),
            )
        )
        mutations = {m.label: m for m in CAMPAIGNS["single-fault"].generate(document)}
        self.assertEqual(
            set(mutations),
            {
                "let-ill-typed-def", "theorem-of-type", "undeclared-universe", "non-positive",
                "field-too-large", "large-elimination-two-ctors", "large-elimination-data-field",
                "undeclared-universe-inductive-type", "undeclared-universe-inductive-ctor",
                "unsafe-in-safe", "unsafe-loop-theorem", "partial-in-safe", "opaque-unfolded",
                "large-elimination-field-inside-index",
            },
        )
        self.assertTrue(all(m.oracle == "guaranteed-reject" for m in mutations.values()))
        for mutation in mutations.values():
            self.assert_well_formed(document.mutated(mutation))

        retagged = document.mutated(mutations["theorem-of-type"])
        self.assertEqual(retagged.lines[-1]["thm"]["name"], 2)
        self.assertNotIn("safety", retagged.lines[-1]["thm"])

        let = document.mutated(mutations["let-ill-typed-def"])
        table = expr_table(let)
        declaration = next(
            line["def"] for line in let.lines if "def" in line and "letE" in table[line["def"]["value"]]
        )
        binding = table[declaration["value"]]["letE"]
        self.assertEqual(binding["type"], binding["value"])
        self.assertEqual(table[binding["value"]], table[declaration["type"]])

        appended = document.mutated(mutations["undeclared-universe"])
        bad = appended.lines[-1]["def"]
        self.assertEqual(bad["levelParams"], [])
        use = expr_table(appended)[bad["value"]]["const"]
        levels = {line["il"]: line for line in appended.lines if "il" in line}
        self.assertIn("param", levels[use["us"][0]])

    def test_field_inductive_serializes_its_own_recursor(self) -> None:
        for fault in FIELD_FAULTS:
            changed = append_field_inductive(self.document, fault)
            self.assert_well_formed(changed)
            block = changed.lines[-1]["inductive"]
            (rec,) = block["recs"]
            (ctor,) = block["ctors"]
            self.assertEqual(rec["rules"], [{"ctor": ctor["name"], "nfields": 1, "rhs": rec["rules"][0]["rhs"]}])
            self.assertEqual(block["types"][0]["isRec"], fault == "non-positive")

    def test_undeclared_inductive_binds_its_universe_only_in_the_control(self) -> None:
        for site in UNDECLARED_INDUCTIVE_SITES:
            for declared in (False, True):
                changed = append_undeclared_inductive(self.document, site, declared)
                self.assert_well_formed(changed)
                block = changed.lines[-1]["inductive"]
                (ty,), (ctor,), (rec,) = block["types"], block["ctors"], block["recs"]
                names = {line["in"]: line["str"]["str"] for line in changed.lines if "in" in line and "str" in line}
                expected = ["u"] if declared else []
                self.assertEqual([names[n] for n in ty["levelParams"]], expected)
                self.assertEqual([names[n] for n in ctor["levelParams"]], expected)
                self.assertEqual([names[n] for n in rec["levelParams"]], (["u_1"] if site == "type" else []) + expected)

    def test_rename_spares_names_the_kernel_recognizes(self) -> None:
        names = [{"in": 1, "str": {"pre": 0, "str": "outParam"}}, {"in": 2, "str": {"pre": 0, "str": "Nat"}},
                 {"in": 3, "str": {"pre": 2, "str": "add"}}, {"in": 4, "str": {"pre": 0, "str": "myDef"}}]
        document = Document((META, *names))
        self.assertEqual([rename_safe(document, n) for n in (1, 3, 4)], [False, False, True])

    def test_safety_and_index_faults_differ_from_their_controls_in_one_place(self) -> None:
        for fault in SAFETY_FAULTS:
            bad, good = append_safety_fault(self.document, fault), append_safety_fault(self.document, fault, True)
            self.assert_well_formed(bad)
            self.assert_well_formed(good)
            self.assertEqual(len(bad.lines), len(good.lines))
        bad, good = append_index_elimination(self.document), append_index_elimination(self.document, True)
        self.assert_well_formed(bad)
        self.assert_well_formed(good)
        (ctor,) = next(line["inductive"] for line in reversed(bad.lines) if "inductive" in line)["ctors"]
        index = expr_table(bad)[expr_table(bad)[ctor["type"]]["forallE"]["body"]]["app"]["arg"]
        self.assertIn("forallE", expr_table(bad)[index])

    def test_extra_recursor_copies_the_first_recursor_under_a_new_name(self) -> None:
        from pathlib import Path

        seed = Document.load(Path(__file__).resolve().parents[1] / "corpus/good/boolprop-valid.ndjson")
        (mutation,) = [m for m in CAMPAIGNS["single-fault"].generate(seed) if m.label == "extra-recursor"]
        changed = seed.mutated(mutation)
        self.assert_well_formed(changed)
        block = next(line["inductive"] for line in changed.lines if "inductive" in line)
        first, copy = block["recs"]
        self.assertEqual({k: v for k, v in first.items() if k != "name"}, {k: v for k, v in copy.items() if k != "name"})
        names = {line["in"]: line["str"] for line in changed.lines if "in" in line and "str" in line}
        self.assertEqual(names[copy["name"]], {"pre": first["name"], "str": "pestycydCopy"})

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


class LiteralArithTests(unittest.TestCase):
    def test_python_oracle_matches_kernel_conventions(self) -> None:
        from pestycyd.campaigns import LITERAL_OPS

        self.assertEqual(LITERAL_OPS["Nat.sub"](2, 3), 0)
        self.assertEqual(LITERAL_OPS["Nat.div"](7, 0), 0)
        self.assertEqual(LITERAL_OPS["Nat.mod"](7, 0), 7)
        self.assertEqual(LITERAL_OPS["Nat.gcd"](0, 0), 0)
        self.assertEqual(LITERAL_OPS["Nat.pow"](0, 0), 1)
        self.assertEqual(LITERAL_OPS["Nat.log2"](0), 0)
        self.assertEqual(LITERAL_OPS["Nat.log2"](2**64), 64)
        self.assertEqual(LITERAL_OPS["Nat.pred"](0), 0)

    def test_needs_the_constants_it_mentions(self) -> None:
        from pestycyd.campaigns import CAMPAIGNS

        self.assertEqual(list(CAMPAIGNS["literal-arith"].generate(Document(({"meta": {}},)))), [])
