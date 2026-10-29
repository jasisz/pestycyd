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
  accept/reject verdicts still count for differentials.
- con-leche/con-ron **derive recursor rules and ignore serialized
  `rules[].rhs`** entirely (probe: `rhs` pointing at `Sort` still accepts).
  Any mutation confined to serialized rec-rule payload fields yields
  `con-*=accept` vs `reject` elsewhere — expected conformance divergence,
  not a bug (same family as the withdrawn prop-recursor report).
- pestka and lean4lean both resolve re-bound intern ids first-binding-wins
  (`intern-table-shadowing`); con-* decline them, nanoda panics.
- `leanchecker --from-export` is the reference oracle: Pestka has exact
  parity with it on all 613 `/private/tmp/level-diff-*` probes; lean4lean
  over-accepts 28 (folds `imax(u+1,1)→u+1` past Lean's def-eq).
- Serialized-field authority split (probed): official *re-derives* inductive
  metadata — `types[].all`, `numNested`, `numIndices`, `numParams`, `isRec`,
  `isReflexive` mutations are all accepted even when wrong — but *validates*
  `recs[].all` order. Pestka validates all of them (stricter than reference,
  ~74 officially-valid rejections); lean4lean/con-* derive all of them;
  nanoda derives `all`-as-set and misses the `recs[].all` order check.
- `findings` prints a `campaign × status-vector` signature rollup — use it
  to triage large stores before reading individual cases.
