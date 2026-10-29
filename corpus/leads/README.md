# Composition leads

These inputs reached interesting checker paths but are not independently
claimed as soundness regressions. They stay separate from `regressions/` so a
matrix disagreement cannot be mistaken for a proof that one checker is wrong.

**Versioning note (2026-10-29):** the `nanoda_bin` in the matrix is a stale
snapshot (~Oct 12) predating upstream nanoda fixes PR #45–#65 (Oct 23 sync
point `a3ef25a`). Every nanoda-acceptance lead below was re-tested against a
fresh `nanobruijn` build carrying all upstream ports — nanobruijn rejects the
forged-field class (`nfields`, `proj.typeName`, `all` duplicates, `recs` name
lies). The entries remain true for the old binary and as regression seeds.

**Fresh-binary arbitration** (all 4853 stored findings re-run through
nanobruijn, correlated with `leanchecker`): official-reject + nanobruijn-accept
= 463, of which 458 are the duplicate-table-index leniency class — **nanobruijn
also resolves `in`/`il`/`ie` positionally**, joining pestka/lean4lean in the
lenient group vs official/con-* strict. The remaining 5 are `recs[].all`
order swaps (still a set on master — PR #65 validates coverage/duplicates but
**not order**) and one η-variant recursor rule rhs (`λmotive.λminor.λt.minor t`
→ `λmotive.λminor.minor`): nanobruijn validates serialized rules by **full
def_eq** (η included) while the reference kernel compares more strictly —
semantically valid acceptance, not a hole. Nanobruijn is also *stricter* than
the reference on derived metadata (`types[].all` duplicates, `numIndices`,
`numNested`, `isRec`) — completeness-direction.

Arbitration note (2026-10-29 sweep of all 4807 stored findings through
`leanchecker --from-export`):

- official accepts & pestka accepts (30): nanoda-crash + con-* `recs-omit`
  findings; no new family.
- official accepts & pestka rejects (130): completeness direction; the
  reference kernel re-derives `types[].all`, `numNested` (accepted even at
  `2^64-1`), `numIndices`, `numParams`, `isRec`, `isReflexive` — pestka
  validates them.
- official rejects & pestka accepts (933): all duplicate-`ie` parser leniency
  (see `pestka-lean4lean-dup-ie-lastwins` below); no semantic divergence.
- official rejects & pestka rejects (3714): agreement; findings exist because
  other checkers crashed or diverged.

The reference kernel validates `recs[].all` and the recursor *type* and rule
RHS *values* via def-eq; it re-derives the fields above and ignores
contradictory serialized metadata.

| Input | Why retained | Related upstream report |
| --- | --- | --- |
| `nanoda-prop-rule-forged.ndjson` | Forged proposition recursor rule; useful for combining proof irrelevance with later rule application. | Related family: [sokonanoda #7](https://github.com/intgrah/sokonanoda/issues/7). |
| `cyclic-rec-rule-seed.ndjson` | Seed for cyclic and self-referential recursor-rule mutations. | Not filed as an independent bug. |
| `nested-name-shadow-seed.ndjson` | Seed for temporary nested-name capture across later declarations. | Final exploits: [nanoda #74](https://github.com/ammkrn/nanoda_lib/issues/74), [sokonanoda #10](https://github.com/intgrah/sokonanoda/issues/10), Arena [PR #308](https://github.com/leanprover/lean-kernel-arena/pull/308). |
| `recursor-rule-swap-0.ndjson`, `recursor-rule-swap-1.ndjson` | Adjacent proposition recursor-rule RHS swaps for differential mutation. | Related family: [sokonanoda #7](https://github.com/intgrah/sokonanoda/issues/7). |
| `prop-recursor-derived-field-swap.ndjson` | Negative control with swapped serialized RHS fields for a `Prop` recursor. Some checkers derive and ignore these convenience fields, so their acceptance is not a soundness finding even though an exact-metadata adapter rejects the file. | Reports withdrawn after clarification in [Nanoda #76](https://github.com/ammkrn/nanoda_lib/issues/76#issuecomment-6478924178) and [Sokonanoda #11](https://github.com/intgrah/sokonanoda/issues/11#issuecomment-6478681676). |
| `trusted-nat-primitive-false.ndjson` | Closed `False` control built by redefining a native `Nat` primitive. Official Lean, Pestka, Nanoda-family, Sokonanoda and Tenet accept it because native reduction trusts selected Init names; it is not a Tenet finding. | Lean's trusted-Init boundary; retained only as a mutation seed. |
| `con-rec-rule-lam-domain.ndjson` | `lam` domain inside a serialized recursor-rule RHS replaced by a recursor `const`. con-leche and con-ron accept; Pestka old/next and Lean4Lean reject `invalid recursor`. Probe result: con-* accept even `rhs` pointing at `Sort`, so they derive rules and ignore serialized RHS fields entirely — their acceptance is by design, not a bug. Retained as a mutation seed for the serialized-rule class. | Same derived-field family as `prop-recursor-derived-field-swap` and the reports withdrawn under [Nanoda #76](https://github.com/ammkrn/nanoda_lib/issues/76#issuecomment-6478924178). |
| `pestka-imax-literal.ndjson` | `imax(succ u, 1)` nested inside a `forallE` codomain (≡ `corpus/probes/level-diff/level-diff-10.ndjson`). Initially looked like a Pestka completeness bug (Pestka alone rejected). **The official Lean kernel also rejects it** (`imax (imax (u+1) 1) v` ≠ `imax (max (u+1) u) v` under Lean's def-eq). Full 613-file sweep: official and Pestka agree on every probe; **lean4lean over-accepts 28 officially-invalid documents**, con-leche accepts all 28, nanoda accepts 16 and panics on 12. The gap is `imax`/`max` normalization: lean4lean/con-* fold `imax(u+1,1) → u+1`, which the reference kernel leaves unfolded. | Confirmed over-acceptance family against lean4lean + con-* (+nanoda); Pestka has exact parity with the reference kernel on all 613 level probes. |
| `pestka-numindices-strict.ndjson` | `numIndices: 0→1` on `LALProofParameterSwap` (Prop inductive). Official kernel and lean4lean/con-* re-derive index counts and accept the inconsistent doc; **Pestka (all four implementations) rejects** `does not match the one the kernel derives`. Pestka validates serialized metadata the reference kernel ignores — completeness-direction divergence, not a bug in either direction by itself. | Pestka stricter than reference on `numIndices`; useful probe for which metadata fields each checker validates vs derives. |
| `con-recs-omit-strict.ndjson` | Mutual inductive (2 types) serializes only 1 of its 2 recursors. Official kernel derives the missing eliminator and accepts; Pestka and lean4lean accept too; **con-leche and con-ron reject**. The formally-verified checkers treat the `recs` list as authoritative-complete while deriving its contents — a completeness-direction divergence the lenient-group filter must NOT suppress (lone rejection is the detector direction). | con-* completeness gap candidate: `recs-N-omit` docs are officially valid. |
| `nanoda-rule-rhs-wrong-arg.ndjson` | `BoolProp.rec`'s `b`-rule RHS lambda binder annotated `motive a` instead of `motive b`. Official, Pestka, lean4lean reject; nanoda and con-* accept. Escalation **attempted and closed**: nanoda validates every semantically loaded field — `assert_nonnested_recursors_def_eq` def-eqs the serialized recursor *type* (binders AND codomain) against the re-derived one, and `assert_nonnested_rec_rule_def_eq` def-eqs rule RHS *values* (`assert_def_eq` at `tc.rs:955`, panic not graceful reject). What's unvalidated is rhs-lambda *binder annotations* — inert, they don't affect iota reduction or value typing. Every closed-`False` route needs a lie exactly where def_eq looks; confirmed by experiment: forged binder, forged codomain, and codomain=`F` variants all panic on the inductive block alone. | Conformance divergence only — nanoda skips a check the reference performs, but the gap carries no proof-witness payload. Robustness finding remains: nanoda panics (`tc.rs:955`) instead of cleanly rejecting invalid recursors. |
| `pestka-lean4lean-dup-ie-lastwins.ndjson` | UPDATE 2026-10-29: **fixed in pestka** — `3ef11a3` ("An index bound twice is refused") adds the check to `addName`/`addLevel`/`addExpr` in `export/tables.av`; verified end-to-end: a fresh native build now rejects `expression index 200 is already bound`, matching official and the Aver-VM path. len4lean + nanobruijn remain lenient (accept or panic on position). Original entry: `ie:19` bound twice with different payloads (`app` then `lam`). Official kernel and con-* hard-reject (`Expr index bound twice` / `already bound`); nanoda panics (`duplicate Expr`); **pestka and lean4lean accept**. Probed further: pestka resolves index bindings **positionally** — a `def` placed before the rebind sees the first payload, one after sees the second (`d : ie0 := Prop` accepted with `ie0` rebound `Sort0→Sort1`). Same goes for `in`/`il` tables. Each declaration still sees one consistent binding state, so it's not a soundness hole — but pestka accepts documents that are internally inconsistent *at the serialization level*, which is stricter a divergence than uniform leniency. Dominant over-acceptance class: ~933 of 4807 arbitrated findings are pestka-accept + official-reject, all duplicate-`ie`. | Conformance note with a real semantic choice: pestka/lean4lean allow mid-file rebinding of index tables; reference kernel treats it as malformed input. Fix candidate for pestka (see arbitration note). |
| `nanoda-all-order-swap.ndjson` | Mutual inductive's recursor `all` list swapped `[1,2]`→`[2,1]`. Official kernel, Pestka old/next/llvm/vm and Lean4Lean reject; nanoda accepts yet panics on structurally malformed `all` variants — it validates the field semantically but not its declared order. Probe: a doc whose `M1.rec` *application* keeps canonical motive order is still accepted under `all=[2,1]`, so nanoda reads `all` as an unordered set — conformance over-acceptance, not a binding exploit. (Swapping the motive args to match the claimed order makes nanoda panic in `tc.rs:955` `def_eq` instead of cleanly rejecting.) **Note the asymmetry in the reference kernel itself: `inductive.types[].all` is re-derived (a `[1,1,2]` duplicate is accepted) while `inductive.recs[].all` is cross-validated — nanoda fails a check the reference performs.** | Nanoda under-validates serialized `all` — confirmed over-acceptance vs the official kernel; same trusted-fields family as [nanoda #47](https://github.com/ammkrn/nanoda_lib/issues/47). |
| `axiom-extra-value-field.ndjson` | `axiom bad : F` carrying a spurious `value` field. Official kernel, Pestka and lean4lean **accept** — their record decoders ignore unknown keys; con-leche rejects (`unknown key`) and nanoda panics (missing `U.rec`, separate issue). Benign: the axiom is an `F`-typed constant either way; the ignored body has no payload channel. | Extra-field leniency class: official/pestka/lean4lean permissive vs con-* schema-strict. Companion to the `axiom bad : F` control — the reference kernel accepts axioms asserting `False` by design. |
| `fake-primitive-nat.ndjson`, `fake-primitive-nat-ctor.ndjson` | Empty `inductive Nat` (and a variant declaring `Nat.evil : F` alongside real `zero`/`succ`) plus `d : Nat := natVal"5"`. Official kernel **accepts** — it recognizes the primitive `Nat` name, installs the builtin primitive and *drops the declared ctors entirely* (`Nat.evil` later resolves to `unknown constant`, so nothing carries a payload). lean4lean rejects (`invalid form for primitive inductive Nat`), con-leche rejects (`reserved basis name`), Pestka accepts the empty shape but **validates declared ctor types** (`invalid return type for 'Nat.evil'`), nanoda panics. Weaponization attempt (`Nat.evil : F` → `bad : F`) fails: the forged ctor is dropped from the env by the reference kernel, not merely ignored for reduction. | Primitive-name special-casing asymmetry: reference installs primitive `Nat` and discards the serialized block's ctors; lean4lean/con-* validate the declared shape. Conformance, not soundness. |
| `lete-nondep-flag-lie.ndjson` | `letE` with `nondep:true` while the body references `bvar0` (the let variable). **Every checker accepts**, including the reference kernel — the flag is inert, let-values are still substituted and the value's type is checked (`let x : Prop := Prop` body ill-typed → uniform reject). | Format probe, closed: `nondep` carries no semantic payload anywhere in the matrix. |
| `nanoda-nested-rec-nfields.ndjson` | Slice of a real `leanexport` document (`Rose` nested via `List`, `List`/`Eq`/`Two`/`E2T`/`Acc2` machinery) with `rules[].nfields` forged `2→3` on the nested-auxiliary recursor `Rose.rec_1`. Official kernel, Pestka and lean4lean reject `invalid recursor Rose.rec_1`; con-* accept (derive family); **nanoda accepts cleanly** — while the same `nfields` lie on a *non-nested* recursor (`Nat.rec`, `inductive.rs:1316`) panics it. Source analysis: iota reduction consumes serialized `nfields` via `major_ctor_args.len().checked_sub(ctor_telescope_size_wo_params).unwrap()` (`tc.rs:1706`) to split params from fields — a lie misbinds ctor args at iota or panics on underflow. Nested aux recursors take the `check_restored_recursor1` path, which in this binary does not compare field counts. **Confirmed real bug class**: upstream nanoda fixed exactly this in PR #63 ("check restored nested recursor field counts", ported to nanobruijn as `5a776fa` adding the `assert_eq` at `inductive.rs:1718` with the comment "Iota reduction uses this count to separate parameters from fields"); our `nanoda_bin` predates the fix. | Real bug, upstream-acknowledged: [nanoda PR #63](https://github.com/ammkrn/nanoda_lib/pull/63). Same trusted-recursor-fields family as [nanoda #47](https://github.com/ammkrn/nanoda_lib/issues/47). Escalation sketch: misbinding feeds ctor-param/field args into wrong rhs binders at iota, storing terms under false type tags — a closed-`False` chain needs a transport through the confused constant and remains unbuilt. |
| `nanoda-proj-typename-forged.ndjson`, `nanoda-proj-typename-anon.ndjson` | Real-slice `proj` with `typeName` forged `PProd→Nat` (a non-structure) and `typeName=0` (anonymous). Official kernel, Pestka, lean4lean and con-* all reject `invalid projection`; **nanoda accepts both** — it does not check that `typeName` names the structure the `struct` argument actually has. During iota/projection reduction the forged name steers field extraction at the wrong type — same misbinding primitive class as the nfields gap. | Real bug, upstream-acknowledged: [nanoda PR #48](https://github.com/ammkrn/nanoda_lib/pull/48) "check projection type name" — our binary predates it. |
| `nanoda-rec-all-dup.ndjson` | `Nat.rec` with `all:[Nat,Nat]` (duplicate block member). Official kernel and Pestka reject `invalid recursor`; **nanoda accepts** — it reads `all` as an unordered set *without cardinality*, so duplicates pass. Known companion to `nanoda-all-order-swap` (order also ignored) — the binary lacks PR #65's parser check that `all`/`ctors` cover exactly the block's members. Payload-wise `all` duplicates look inert; retained as conformance-over-acceptance evidence. | Nanoda under-validates serialized `all` — upstream-acknowledged class: [nanoda PR #65](https://github.com/ammkrn/nanoda_lib/pull/65). |
| `nanoda-nat-rule-rhs.ndjson` | Real-slice predecessor of `nanoda-rule-rhs-wrong-arg`: forged rule RHS on `Nat.rec`. Fresh matrix (2026-10-29): **unanimous reject** (`Invalid recursor Nat.rec`), nanobruijn included. | Closed; kept as a seed for the serialized-rule class. |
| `con-rose-rec1-ruleswap.ndjson` | `Rose.rec_1` with its `rules` order swapped. All checkers reject `Invalid recursor`; **con-leche/con-ron accept** — they re-derive rules and ignore the serialized ones (see "second-crossing" below). | Same derive-by-design family as `con-rec-rule-lam-domain`. |

When one of these is escalated to a closed false proof, move the minimized
case to `regressions/` and add the exact upstream issue rather than merely a
related-family link.

## Klasa `quot` — brak quotient post-check (2026-10-29)

Prawdziwy slice `Quot`/`Quot.mk`/`Quot.lift`/`Quot.ind` (+ `Eq`) z eksportu S1 — `corpus/real/slice-s4`-probes w `corpus/leads/quot-*.ndjson`.

Pliki (świeża macierz 2026-10-29; con-* wszędzie `decline`):

| plik | mutacja | official | lean4lean | nanobruijn | pestka |
|---|---|---|---|---|---|
| `quot-q-kind-lift2ctor` | `kind` lift→ctor | reject | **accept** | **accept** | reject |
| `quot-q-lift-lp` | `lift.levelParams` zmienione | reject | **accept** | **accept** | reject |
| `quot-q-lift-type-swap` | `lift.type` := typ konstruktora | reject | **accept** | reject | reject |
| `quot-q-evil-lift-prop` | extra `quot` na obcej nazwie | **accept** | accept | reject | reject |
| `quot-q-evil-use` | j.w. + użycie stałej | reject (`unknown constant`) | reject | reject | reject |
| `quot-qred-honest` | uczciwa redukcja `Quot.lift f h (Quot.mk r a) ≡ f a` | — | — | — | accept |
| `pestka-quot-dup-record` | duplikat rekordu `Quot.lift` | reject | reject | crash | reject (po fixie) |

Warianty `qred-*` z fałszowanymi metadanymi leżą w `corpus/probes/`.

| mutacja | official | lean4lean | nanobruijn | pestka | con-* |
|---|---|---|---|---|---|
| `kind` na złą rolę (lift→ctor, mk→ind, ind→type, type→lift) | reject "Quotient constant mismatch" | **accept** | **accept** | reject | decline/impl |
| `lift.levelParams` skrócone/zmienione | reject | **accept** | **accept** | reject | decline |
| `lift.type` := typ konstruktora | reject | **accept** | panic | reject | decline |
| `kind` spoza słownika | reject | reject | panic | reject | reject |
| `quot` dla obcej nazwy (`Quot.evil`) | **accept (ignoruje!)** | accept | panic | **reject** | decline |
| `quot` na nazwie istniejącej deklaracji (`Eq`) | reject | reject | panic | reject | reject |
| **literalny duplikat rekordu `quot` (`Quot.lift` zreplay'owany)** | reject `Duplicate declaration` | reject | crash | ~~accept~~ **reject po fixie `qstated`** | accept |
| omit `ind` | accept | accept | accept | accept | accept |

Wnioski:
- **lean4lean nie implementuje quotient post-check wcale** — akceptuje wszystkie falsyfikacje `kind`/`levelParams`/`type` na prawdziwych rekordach Quot. Najostrzejsze: `lift` z typem konstruktora (tylko l4l akceptuje).
- **nanobruijn** ma częściowy gap: akceptuje kłamstwa `kind`/`levelParams`, odrzuca (panika) podmianę `type`.
- `kind` jest prawdopodobnie **inertną adnotacją** — rola wywodzona z nazwy (l4l bez konfliktu łyka dwa rekordy z tym samym kind). Podmiany `type`/`levelParams` są spójnie-zepsute: każde użycie stałej jest typowane pod złą sygnaturę → payload zablokowany przez typowanie.
- Extra `quot` na nie-Quot nazwach: **nawet oficjalny kernel cicho ignoruje** (stała nie rejestruje się — `unknown constant` przy użyciu). **Pestka jest tu ściślejsza od referencji** — completeness-dywergencja w drugą stronę.
- Kierunek dalszego ataku: `Quot.lift f h (Quot.mk r a) ~> f a` — redukcja quot na dokumencie z sfałszowanymi metadanymi; jeśli jakiś checker wywodzi sloty redukcji z `kind`/lp zamiast z nazwy, misbinding. Typowanie aplikacji (używane przy każdym użyciu) najpewniej osłania.

Rozstrzygnięcie klasy `quot`:
- **Oficjalny kernel i lean4lean nie rejestrują `Quot.*` jako używalnych stałych** — `const Quot.lift` → `unknown constant`. Rekordy quot instalują wyłącznie wewnętrzne reguły redukcji, więc falsyfikacje metadanych **nie mogą nieść payloadu** — brak kanału aplikacyjnego. Klasa w całości konforemacyjna.
- **Pestka traktuje `Quot.*` jako prawdziwe stałe**: uczciwa sonda `qred : Eq (Quot.lift f h (Quot.mk r a)) (f a) := rfl` została zaakceptowana — redukcja quot w pestce faktycznie odpala (witness: `quot-qred-honest.ndjson`). To rozjazd modelowy pestki vs referencja (więcej możliwości), nie bug.
- `quot` na nazwie istniejącej deklaracji (`Eq`, `Quot.mk`) → jednomyślny `Duplicate declaration`.
- `pestka` na extra `quot` (`Quot.evil`) ściślejsza od referencji → znany kierunek completeness.
- **GAP PESTKI — NAPRAWIONY (2026-10-29, hunt14)**: literalny duplikat rekordu `quot` (`Quot.lift` powtórzony identycznym payloadem przed `Quot.ind`) — oficjalny kernel i `leanchecker-paranoid` odrzucają `Duplicate declaration: Quot.lift`, lean4lean odrzuca, nanobruijn crash, con-* akceptują (derive) — a **pestka akceptowała na wszystkich backendach łącznie z VM**. Przyczyna: `addQuotDecl` traktował rekord `quot` jako weryfikację wyprowadzonych stałych (env je już zawiera, więc identyczny replay przechodził porównanie), podczas gdy referencja traktuje każdy rekord jako deklarację nazwy. Fix: `Env.qstated` (`check/state.av`) śledzi nazwy zgłoszone rekordami `quot`; `addQuotDecl` odrzuca powtórkę jako `'X' has already been declared` — zgodnie z oficjalnym `Duplicate declaration`. Zweryfikowane na replay-sondach wszystkich 4 ról (type/ctor/lift/ind → wszystkie reject) i bez regresji na legalnych slice'ach s1–s4, `quot-qred-honest`, `acc2-rec-iota`. Witness: `corpus/leads/pestka-quot-dup-record.ndjson`.
- Uwaga o wiarygodności hunt14: wczesne findingi z werdyktem `pestka=accept` na duplikatach `ie` są artefaktem nieaktualnej binarki (hunt ruszył 15:28, `main` przebudowany 15:34) — świeże backendy odrzucają te dokumenty poprawnie.

## Klasa `primitive-def` — podmiana ciała prymitywu (POZA THREAT MODELEM upstream)

`nonstandard-prelude-nat-add-false.ndjson` / `-eq-0-1.ndjson`: `Nat.add := λa n. a` + sprzeczne tezy `∀x. Eq (add x 2) x` i `Eq (add 2 2) 4` → `Eq 2 4` → `∀P:Prop.P` (i `Eq 0 1` jako kontrola). leanchecker/pestka/nanobruijn akceptują; lean4lean (`invalid form for primitive def`) i con-* (`nonstandard structural Nat operation`) odrzucają.

Szkice: `nat-add-contradiction.ndjson` to wcześniejsza wersja `-false` (bez końcowego `thm`), werdykty identyczne. `nat-add-primitive-body-forgery.ndjson` to wariant na stałych zamiast literałach `natVal`; omija fast-path i jest **jednomyślnie odrzucany**, więc służy jako kontrola.

**Rozstrzygnięte: NIE jest to bug upstream.** lean4#15908 to dokładnie ten przypadek — zamknięte jako „not a bug" (2026-10-24): kernel akceptuje dowód False tylko przy *standardowym preludium*; podmieniony `Nat.add` to niestandardowe preludium (osobny rozdział „Non-standard prelude definitions" w ich przewodniku). Właściwą obroną jest **comparator** (`lake comparator`), który sprawdza, że wbudowane deklaracje zgadzają się z oficjalnym preludium — i łapie ten atak (`Const does not match between challenge and target 'Nat.add'`).

Wnioski dla matrycy:
- Werdykt pestki/nanobruijn `accept` jest tu **zgodny z referencją** — to nie nadakceptacja.
- lean4lean jest **ściślejszy od referencji** (defense-in-depth przez `checkPrimitiveDef`) — legalne, nie bug.
- Nie uogólniać na `Nat.mul`/`sub`/`decide`/`String.*` jako „bugów" — cała klasa jest poza threat modelem.
- Ewentualna walidacja ciał prymitywów w pestce = decyzja produktowa (comparator-like), nie naprawa dziury.
- Potencjalne dziury kernela zgłaszać prywatnie na security@lean-fro.org, nie publicznie.

### `nanobruijn-mdata-panic` (robustness, not soundness)

Any export containing a `{"mdata":{"expr":N,"data":{...}}}` record crashes
fresh nanobruijn at `src/parser.rs:859` (`Expr.mdata not supported` → panic),
while official/pestka/lean4lean accept and treat mdata transparently in
reduction (verified: `Eq Nat (mdata (add 2 3)) 5 := rfl` reduces fine).
con-leche/con-ron decline the record at parse level. Legal Lean export syntax
→ completeness/robustness gap in nanobruijn, no payload.
Witness: `corpus/good/sem-reduction-family.ndjson`.

## tooling: `tools/cross.py` and instrumented nanobruijn (2026-10-29)

**cross.py** merges self-contained leanexport NDJSON documents: `in`/`il`/`ie`
index tables are remapped by disjoint offsets (in:0/il:0 stay implicit),
declaration names are resolved semantically (`Name.anonymous` chains) and
deduplicated first-wins. Validated: 11 slice combinations + good-seed splices,
all unanimously accepted where legal. Field→index-space map is maintained in
the script header (`param` in `il` records is an `in`-ref!).

**Instrumented nanobruijn** (checkout in `/private/tmp/nanobruijn-arena`;
the local change is saved as `adapters/nanoda/nanobruijn-catch-unwind.patch`):
- `declaration_timeout_secs: 120` in `adapters/nanoda/config.json` enables
  upstream's own per-declaration `catch_unwind` — a panicking decl prints
  `PANIC #i: <name>` and is skipped; the run ends with
  `N declaration(s) failed type checking (panicked)` → exit 1 → adapter
  verdict reject. Panics now report WHICH declaration died.
- `src/main.rs`: `cfg.to_export_file()` wrapped in `catch_unwind` so
  parse-time panics (`Expr.mdata not supported` at parser.rs:859, integer
  overflow on absurd metadata) become `exit 1` reject instead of SIGABRT.

Re-run effect on ~4900 historical `nanoda=crash` findings: crashes masked
both verdicts — 30/30 sampled `pestka=accept` cases → nb also **accepts**
(dup-`ie` leniency confirmed), 40/40 sampled `pestka=reject` cases → nb
also **rejects**. No hidden divergences in the sample; `nanoda=crash` cells
should be re-read as "verdict unknown, likely same as pestka".

## second-crossing + metadata-field axes (2026-10-29 pm)

Crossed-seed hunting (`corpus/crossed`, hunt16): all findings so far are the
known classes — dup-`ie` leniency (nb+l4l accept), expr-splice l4l accept,
`forallE`-type splices. Instrumented nb now reports accept/reject instead of
crash in-matrix (e.g. `PANIC #51: Quot` pinpointing `quot.rs:138` unwrap on a
name-mangled `Quot.mk` — official stays lenient on quot names, nb correctly
rejects: a rare case of nb *stricter* than reference).

Hand probes:
- **opaque vs def reduction** (`corpus/probes/d1-tails/{opaque,def}-probe.tail`, appended to `slice-d1`):
  `Eq (String.Internal.append "a" "b") "ab"` by rfl → **unanimous reject**
  (opaque does not unfold); identical probe on `String.append` (def) →
  unanimous accept. Opaque/def boundary unanimous.
- **forged-primitive cross** (`tools/cross.py` of the forged `Nat.add` doc
  FIRST + slice-d1; not stored): unanimous reject at `Nat.succ_le_succ` — symbolic `n+1`
  bypasses fast-path (literal-only) so every kernel unfolds the planted def.
  Confirms all checkers share the same model: name-trusted fast-path on
  literals + def unfold on symbolic args; lean4#15908 does not split the matrix.
- **`k` flag** is validated *both* directions: `Exists.rec k→true` →
  `Invalid recursor` (unanimous); `Eq.rec k→false` → also `Invalid recursor`
  (unanimous) — k must match subsingleton-eligibility exactly.
- **`numMotives`** flip (Rose.rec_1 2→1) → `Invalid recursor`, unanimous.
- **`recs[].rules` order** swap → `Invalid recursor`, unanimous except
  **con-leche/con-ron accept**. `rules[].rhs` → pointed at a `sort` expr:
  con-* **still accept** — con-* re-derive recursor rules from the inductive
  and treat exported rules/rhs as untrusted hints (inert leniency, same
  class as their other derive-by-design gaps). They *do* validate `k` and
  `numMotives`, so the leniency is selective to rule bodies.
