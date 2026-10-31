# Working notes

## Test / verify

- `uv run --locked --with pytest python -m pytest -q` — the venv is editable
  install only; pytest is not a project dependency. Bare `pytest` picks up a
  stray conda pytest that cannot import `pestycyd`.
- `uv run --locked python -m unittest discover -s tests -v` also works (README).

## Local kernel layout (this machine)

`pestycyd.toml` (untracked, machine-local; `pestycyd.example.toml` is the
committed template):

- `pestka-old`, `pestka-next` — `../pestka/.build/target/release/main` with
  `old`/`next` core argument. Verdict `required`.
- `nanoda`, `lean4lean`, `con-leche`, `con-ron` — binaries shipped inside the
  elan toolchain `~/.elan/toolchains/leanprover--lean4---v4.35.0/bin/`.
  nanoda goes through `adapters/nanoda/run` (JSON config + stdin).
- `con-*` exit codes: 0 accept, 1 reject, 3 malformed input → mapped to
  `decline` in config (they never reached semantic checking).
- `pestka-vm` runs via pinned aver `/private/tmp/aver-pinned/target/release/aver`
  (0.31.0-dev; installed 0.24.1 can't parse pestka's sources). It interprets
  `../pestka/main.av` — a genuinely independent implementation, but slow
  (~seconds per input): keep it out of broad hunts, use it on matrices of
  already-interesting candidates. `pestka/aver.toml` needed its obsolete
  `[rust].panic` key removed for aver 0.31.
- `pestka-llvm` is the coverage-instrumented pestka build
  (`../pestka/.build-pestycyd/`) feeding `pestycyd-llvm-feedback`.
- Older toolchains (4.32.0, 4.34.1) under `~/.elan/toolchains/` provide
  older copies of the same checkers for version-differential runs.

`leanexport` (same bin dir) writes lean4export NDJSON to stdout:
`LEAN_PATH=<olean dirs> leanexport Module > out.ndjson`. Full `Init` exports
are ~300 MB; `prelude` files export small but then almost nothing is
available (no `=`, no `CoeFun`) — nontrivial to hand-write.

`/private/tmp` keeps ~800 ndjson artifacts from earlier hunts — a mining
pool for corpus seeds and known-bad cases.

## Hunting lessons

- nanoda panics on any export whose expression table contains
  structurally-equal records (`Attempted to insert duplicate Expr`,
  parser.rs:120) — even valid, validity-preserving outputs (eta/let wraps
  re-emit `bvar:0`). Also `tc.rs def_eq` assertion panics. Robustness class.
  `tolerate = ["crash"]` on `[kernels.nanoda]` suppresses it in hunts
  (per-kernel tolerated severe statuses, `KernelSpec.tolerate`); its
  accept/reject verdicts still count for differentials. But a tolerated
  crash is a *lost* verdict: every wrap-beta/let/eta output used to crash
  nanoda, so metamorphic hunts never tested it. Appending and wrapping
  rewrites now go through `rewrite.share` (one record per structure, as
  lean4export emits); run `share` over any hand-assembled seed too —
  sokonanoda refuses repeated names (`duplicate Name`) the same way.
- con-leche/con-ron **derive recursor rules and ignore serialized
  `rules[].rhs`** entirely (probe: `rhs` pointing at `Sort` still accepts).
  Any mutation confined to serialized rec-rule payload fields yields
  `con-*=accept` vs `reject` elsewhere — expected conformance divergence,
  not a bug (same family as the withdrawn prop-recursor report).
- sokonanoda likewise **installs only the recursors it derives** and drops
  serialized extras: `extra-recursor` copies (and Arena's `rogue`) are
  accepted at the block but absent from the environment (`unknown const
  ….pestycydCopy` on use). Its lone `accept` on `extra-recursor` is
  conformance divergence, not a hole. The same holds for its lone accepts
  on `recs[].*`, `ctors[].levelParams/cidx/numFields` and `types[].ctors`
  mutations (closedness, level-params, inductive-structure): it rebuilds
  all of them from the block (`checker/inductive/mod.rs` `ctors_env_ext`,
  `mk_declars`). It needs `--nat-extension --string-extension`, otherwise
  it *declines* every export with a Nat literal.
- nanoclo's NbE conversion ignores `lam` binder domains, so it admits a
  serialized recursor rule whose RHS differs from the derived one only in
  lambda annotations (official/nanoda master reject: `Invalid recursor`,
  `tc.rs:985`). Inert — the lambdas vanish under iota — same class as the
  `nanoda-rule-rhs-wrong-arg` lead. Erase binder types before comparing
  (scratch `erase.py` pattern) to triage nanoclo-only accepts.
- nanoclo also accepts *swapped* recursor-rule RHS (`recursor-crosswire`
  `swap-adjacent-rhs-*`) — but only for recursors eliminating into `Prop`.
  There the swapped RHS is def-eq to the derived one by proof irrelevance
  once lambda domains are ignored; on `Type` families nanoclo rejects every
  swap (43/43 in the generated-seed hunt). Inert, same family as the
  withdrawn nanoda #76 / sokonanoda #11 reports. Left untriaged on purpose:
  a rule cannot yet tell `Prop` from `Type` recursors.
- nanobruijn (`nanoda` in `.pestycyd/all-checkers.toml`) panics at
  `inductive.rs:32` on every mutual block with a non-recursive member: it
  recomputes `isRec` per type, Lean flags the whole block. Reported as
  nanobruijn#2; upstream nanoda fixed it silently in 05024bd. About 30% of
  `generate nested` seeds hit it, so expect it in `nested` hunts.
- `leanchecker --from-export`, `leanchecker-paranoid` and `lean4lean --import`
  reject valid exports with `unknown constant` when a mutual block's later
  member uses a constant in its type that no constructor mentions, and hash
  order reaches an earlier member first (lean4#16133, `Lean/Replay.lean`;
  fixed on lean4 master by #16138, still in 4.35.0 and in lean4lean's own
  `Lean4Lean/Replay.lean` copy).
  The official verdict is then wrong: check `unknown constant` rejections
  against the export before trusting them as the expected status.
- The same three reject valid exports that use `Quot.mk`/`Quot.lift`/`Quot.ind`
  without naming `Quot` (`unknown constant 'Quot.lift'`, name-dependent):
  `checkExport` erases those names from the replay map, so nothing forces
  `Quot` in first. Already reported as lean4#15643 and lean4lean#66.
- lean4lean validates the *bodies* of Nat primitives (`invalid form for
  primitive def Nat.gcd`) through Init helpers it looks up by name (`ite`,
  `HMod.hMod`, `OfNat.ofNat`, `rfl`, `WellFounded.Nat.fix`, `Bool.casesOn`,
  ...): metamorphic rewrites of those, which official accepts, make it
  reject. Stricter than reference by design; hunt with `--protect-prelude`.
- The nanoda family (nanoda, nanoda master, nanoclo, sokonanoda) parses
  `hints.regular` as u16 (`expected u16`): a height above 65535 is refused at
  parse time, though Lean's is UInt32. `metamorphic-delta`'s
  `def-hints-regular-max` hits it on every seed; triaged, not reported (Lean
  never computes such heights in practice).
- Hunt nano-lean's fixtures with `--finding-require-seed-change`:
  `primitives.ndjson` (lean4#15643) and `forged-nat-add.ndjson` (a forged
  `Nat.add` proving `False`) already diverge as seeds.
- con-leche/con-ron treat theorem bodies as opaque and rescue `And.rec` on
  stuck proofs by the *name* `And` (README, OVERVIEW §3): `namespace-shuffle`
  renaming `And` makes them reject `theorem-reduction.ndjson`. Documented.
- `namespace-shuffle` rediscovers lean4#16133 and lean4#15643 unaided; triage
  overturns official's verdict when a rule with `expected` explains it.
- nano-lean (`nl-fast`, `nl-ref`, `nl-fast --term-core`; sdiehl/nano-lean,
  binaries in /private/tmp/nano-lean-bin) is exact on all 613 level probes
  (official rejects 50 semantically equal pairs), rejects forged data-type
  rules and false theorems they would prove, and passes its own
  `derivecheck` build on every corpus input. It is stricter than the
  reference on export metadata (`all` groups, counts, omitted recursors).
- nanoda master accepts serialized recursor rules equal to the derived ones
  up to definitional equality, including structure eta: a minor nobody
  reaches (the inner recursor's major is a fieldless structure) may be
  anything. Forged rules that change a computed value are still refused.
- tenet (and nanoda master) need all four quotient constants declared:
  without `Quot.ind` tenet never reduces `Quot.lift` and rejects `funext`,
  nanoda master crashes. `corpus/real/slice-d1.ndjson` used to lack it (a
  slicing artefact; lean4export always emits all four) and now carries it.
- pestka and lean4lean both resolve re-bound intern ids first-binding-wins
  (`intern-table-shadowing`); con-* decline them, nanoda panics.
- `leanchecker --from-export` is the reference oracle: Pestka has exact
  parity with it on all 613 `corpus/probes/level-diff/` probes; lean4lean
  over-accepts 28 (folds `imax(u+1,1)→u+1` past Lean's def-eq).
- Serialized-field authority split (probed): official *re-derives* inductive
  metadata — `types[].all`, `numNested`, `numIndices`, `numParams`, `isRec`,
  `isReflexive` mutations are all accepted even when wrong — but *validates*
  `recs[].all` order. Pestka validates all of them (stricter than reference,
  ~74 officially-valid rejections); lean4lean/con-* derive all of them;
  nanoda derives `all`-as-set and misses the `recs[].all` order check.
- `findings` prints a `campaign × status-vector` signature rollup — use it
  to triage large stores before reading individual cases.
- `src/pestycyd/triage.toml` is the machine-readable form of the lessons
  above: once a divergence class is understood, add a narrow rule (prefer
  `sites`/`output`/`reference` over kernel names) so hunts stop surfacing
  it. Check a new rule against the archive (`.pestycyd/*/findings`) — it
  should explain the class and nothing else.
