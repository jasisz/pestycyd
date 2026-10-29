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

