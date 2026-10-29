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
- `pestka-vm` is disabled: installed aver 0.24.1 cannot parse pestka's
  sources (pinned aver is newer). Re-enable after upgrading aver.
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
  re-emit `bvar:0`). Also `tc.rs def_eq` assertion panics. Robustness class;
  use `--semantic-only` on differential campaigns to cut the noise, keep
  robustness on for guaranteed-accept campaigns.
- con-leche/con-ron **derive recursor rules and ignore serialized
  `rules[].rhs`** entirely (probe: `rhs` pointing at `Sort` still accepts).
  Any mutation confined to serialized rec-rule payload fields yields
  `con-*=accept` vs `reject` elsewhere — expected conformance divergence,
  not a bug (same family as the withdrawn prop-recursor report).
- pestka and lean4lean both resolve re-bound intern ids first-binding-wins
  (`intern-table-shadowing`); con-* decline them, nanoda panics.
- `findings` prints a `campaign × status-vector` signature rollup — use it
  to triage large stores before reading individual cases.
