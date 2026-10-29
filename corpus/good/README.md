# Valid mutation seeds

These small exports are accepted by the official Lean kernel and are intended
as starting points for focused mutation campaigns. They avoid `Init`, trusted
primitive reductions, inductives, and imported recursors whenever possible.

| Input | Purpose |
| --- | --- |
| `dependent-id.ndjson` | Minimal dependent `Pi`/lambda seed. `expression-structure-full` on this input found MathGraph's closure-mode comparison bug. |
| `proof-param-rec-consumer.ndjson` | Universe-polymorphic proof-parameter recursor with a real downstream consumer, so serialized recursor mutations must survive end-to-end checking instead of dying as unconsumed metadata. |
| `mutual-ind-order.ndjson` | Two-type mutual inductive block with recursors; stresses mutual ordering, shared `all` lists, and cross-type ctor references. |
| `mutual-nested-order.ndjson` | Mutual inductives with nested occurrences; larger block for ordering and nested-parameter campaigns. |
| `mut-param-small.ndjson` | Small parameterized mutual inductive without declarations; exercises inductive metadata paths only. |
| `nested-uv.ndjson` | Four-block nested inductive family with universe variation, for nested-`uv` recursor-rule surface. |
| `widek-100.ndjson` | Wide K-recursor guard case: many `Prop` parameters feeding one K-elimination. Stresses `numParams`-scale code paths. |
| `nat-ops-small.ndjson` | `Nat` primitive operations across ~200 definitions; trusted-reduction surface for `Nat.add`/`Nat.div` and friends. |
| `deep-129-outer.ndjson` | Deep binder chain (129 nested `Pi`/`lam`); stresses loose-bvar range tracking and binder-depth bookkeeping. |
| `boolprop-valid.ndjson` | Small `Bool`/`Prop` inductive with recursor use; the clean control for Bool/Prop recursor mutations. |
| `cyclic-rec.ndjson` | Recursor rule whose RHS recursively references the recursor itself; seed for cyclic-rule campaigns. |
| `indexed-prop.ndjson` | Indexed `Prop` family with four inductive blocks; exercises index-threaded recursor rules. |
| `minimal-proof-irrelevance.ndjson` | Minimal proof-irrelevance transport across non-standard axioms; con-* decline it by design (`not implemented yet: non-standard axiom`). |
| `swapbox.ndjson` | Compact declaration pair sharing a boxed universe parameter; seed for level-param swap campaigns. |
| `reversed-reference.ndjson` | Well-formed input whose record order is reversed against the usual emission order; stresses position-independent checking. |

| `mutual-recursor-application.ndjson` | `cyclic-rec` plus a def that actually applies `M1.rec` with both mutual motives and all three minors — the first seed exercising eliminator *use*, not just declaration. |
| `iota-forest-mutual.ndjson` | Real-export slice: `Forest.rec` mutual iota on `fcons` chains — inner recursion through `Tree.rec` + `Nat.add` in the minor. Unanimously accepted. |
| `iota-rose-mutual.ndjson` | `Rose.rec`/`Rose.rec_1` nested-recursor reduction over `List (Rose Prop)` — the aux rec folds the list; direct `rec_1` invocation too. Unanimously accepted. |
| `inst-chain-brecon.ndjson` | Instance-projection chains (`hAdd→instHAdd→Add.add→instAddNat→Nat.add`, `ofNat→instOfNatNat→natLit`) plus `Nat.brecOn`/`below` course-of-values reduction on a literal. |
| `sem-reduction-family.ndjson` | Mixed reduction probes on the s3 slice: symbolic iota (`add x 2 ≡ succ (succ x)`, `add x 0 ≡ x`), nested `proj` chains, `mdata`-transparent reduction, nested `letE` zeta, plus `add_sym_bad` as the unanimously-rejected control. NOTE: nanobruijn *panics* on the `mdata` record (`parser.rs:859` — mdata unsupported) and con-* decline it; strip the `mdata_chain` decl for a strictly-portable seed. |
| `acc2-rec-iota.ndjson` | `Acc2.rec` (Acc-family eliminator into `Sort u`) iota on a legal term: `Acc2.rec motive minor x (intro x h) ≡ Two.mk Type` with the full `ih` argument (`∀y p. motive y (h y p)`) correctly instantiated. Unanimously accepted; the unanimously-rejected `acc2_iota_neg` control is `corpus/probes/acc2-iota-neg.ndjson`. Closes the `Acc.rec`/subject-reduction axis on legal terms — any residual disagreement here is documented non-transitivity/completeness, not a reportable soundness bug (HackMD guide). |
| `eta-pp.ndjson` | Structure eta on `PProd`: `PProd.mk p.1 p.2 ≡ p` in both orientations via `rfl` under a binder — unanimous. Closes the structure-eta family. |
| `unit-eta.ndjson` | Unit eta at three levels: `PUnit.{0}` (Prop), `PUnit.{1}` (Type), and `True` — `∀p. Eq p unit := rfl` — unanimous. |
| `acc2-prop-iota.ndjson` | `Acc2.rec` with a Prop-valued motive (`λa t. Acc2 Prop r a`, `u=0` subsingleton elimination): `rec ... (intro x h) ≡ Acc2.intro x h` via `rfl` — unanimous; completes the Acc-family matrix (Type + Prop motives). |
| `quotord5-indlift.ndjson` | `quot` record order permuted `type,ctor,ind,lift` (the only other order preserving name/expr binding) — accepted by all incl. official+paranoid: canonical order is NOT required, records verify independently per-name. Confirms the `qstated` duplicate-marking fix in pestka models reference semantics exactly. |
