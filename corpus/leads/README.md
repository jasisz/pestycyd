# Composition leads

These inputs reached interesting checker paths but are not independently
claimed as soundness regressions. They stay separate from `regressions/` so a
matrix disagreement cannot be mistaken for a proof that one checker is wrong.

| Input | Why retained | Related upstream report |
| --- | --- | --- |
| `nanoda-prop-rule-forged.ndjson` | Forged proposition recursor rule; useful for combining proof irrelevance with later rule application. | Related family: [sokonanoda #7](https://github.com/intgrah/sokonanoda/issues/7). |
| `cyclic-rec-rule-seed.ndjson` | Seed for cyclic and self-referential recursor-rule mutations. | Not filed as an independent bug. |
| `nested-name-shadow-seed.ndjson` | Seed for temporary nested-name capture across later declarations. | Final exploits: [nanoda #74](https://github.com/ammkrn/nanoda_lib/issues/74), [sokonanoda #10](https://github.com/intgrah/sokonanoda/issues/10), Arena [PR #308](https://github.com/leanprover/lean-kernel-arena/pull/308). |
| `recursor-rule-swap-0.ndjson`, `recursor-rule-swap-1.ndjson` | Adjacent proposition recursor-rule RHS swaps for differential mutation. | Related family: [sokonanoda #7](https://github.com/intgrah/sokonanoda/issues/7). |
| `prop-recursor-derived-field-swap.ndjson` | Negative control with swapped serialized RHS fields for a `Prop` recursor. Some checkers derive and ignore these convenience fields, so their acceptance is not a soundness finding even though an exact-metadata adapter rejects the file. | Reports withdrawn after clarification in [Nanoda #76](https://github.com/ammkrn/nanoda_lib/issues/76#issuecomment-6478924178) and [Sokonanoda #11](https://github.com/intgrah/sokonanoda/issues/11#issuecomment-6478681676). |
| `trusted-nat-primitive-false.ndjson` | Closed `False` control built by redefining a native `Nat` primitive. Official Lean, Pestka, Nanoda-family, Sokonanoda and Tenet accept it because native reduction trusts selected Init names; it is not a Tenet finding. | Lean's trusted-Init boundary; retained only as a mutation seed. |
| `con-rec-rule-lam-domain.ndjson` | `lam` domain inside a serialized recursor-rule RHS replaced by a recursor `const`. con-leche and con-ron accept; Pestka old/next and Lean4Lean reject `invalid recursor`. Probe result: con-* accept even `rhs` pointing at `Sort`, so they derive rules and ignore serialized RHS fields entirely — their acceptance is by design, not a bug. Retained as a mutation seed for the serialized-rule class. | Same derived-field family as `prop-recursor-derived-field-swap` and the reports withdrawn under [Nanoda #76](https://github.com/ammkrn/nanoda_lib/issues/76#issuecomment-6478924178). |

When one of these is escalated to a closed false proof, move the minimized
case to `regressions/` and add the exact upstream issue rather than merely a
related-family link.
| `pestka-imax-literal.ndjson` | `imax(succ u, 1)` nested inside a `forallE` codomain; every other kernel folds it to `succ u` and accepts, Pestka rejects `declaration type mismatch`. One of ~30 level-probe vectors where Pestka alone rejects, so its `imax`/`max` normalization has a completeness gap on literal second arguments. | Pestka-side completeness bug candidate; probed during the `level-diff` investigation, still reproduces on the current build. |
