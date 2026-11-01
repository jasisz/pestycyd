# scale_gen

Scale ladders: self-contained valid NDJSON exports (built from `Sort` alone,
no prelude) whose size grows along one axis, for robustness and performance
divergences rather than soundness.

```bash
python3 tools/scale_gen/gen.py /tmp/scale --depths 1000,10000,100000
python3 tools/scale_gen/run.py /tmp/scale/*.ndjson --timeout 60 --out /tmp/scale.jsonl
```

Shapes: universe chains (`level_succ`, `level_max_nest`, `level_imax_nest`,
`level_eq_reassoc`, `many_level_params`), binder chains (`arrow_chain`,
`dep_pi_chain`, `first_binder`), `let_chain`, `let_ref_chain` (type is the
last `let` variable, so the check zeta-reduces the whole chain), `beta_chain`,
`delta_chain` / `delta_chain_both` (n definitions, each unfolding to the
previous), `long_name`, `wide_decls`, `app_wide`. `run.py` records exit
status, signal, wall time and the output tail for every configured kernel.

Every export is valid, so a non-zero exit is a decline, a crash or a
completeness failure. Most at 100k are deliberate limits: `u16` binder and
level indices in the nanoda family and sokonanoda, kefir's 65536-record cap,
nano-lean's declaration stack budget.

## Results (2026-11-01, 1k/10k/100k)

- **lean4lean rejects `delta_chain` from n = 1000** ("deterministic
  timeout"): `FuelConfig.lazyDelta` defaults to 1000 steps for one
  `lazyDeltaReduction` call, which has no bound in the C++ kernel. A plain Lean
  file of 1200 chained `def Dk : Prop := D(k-1)` and `theorem chain : D1200 :=
  trivial` (needs `set_option maxRecDepth 10000`) is accepted by the other 15
  checkers. `--config:lazyDelta=100000` makes lean4lean accept it. The Arena's
  `arena` branch has the same default.
- `let_chain` 100k: pestka-next 57 s (10k: 0.7 s), pestka-old 0.1 s.
  `let_ref_chain` 100k: pestka-old, pestka-next, con-leche and tenet time out at
  60 s; official 0.5 s. `first_binder` 100k: pestka-next 41 s, con-leche 21 s.
- `beta_chain` 100k: official 11 s, lean4lean 12 s, sokonanoda 31 s (the
  Arena's `beta-ladder` covers this).
- nanoda-master panics with `attempt to add with overflow` (`util.rs:627`) on
  100k-deep arrows; nanobruijn does not.
- The nanoda family and sokonanoda panic in the parser when a declared universe
  parameter has no `param` level record; Lean's elaborator rejects unused
  universe parameters, so only hand-built exports reach this.
