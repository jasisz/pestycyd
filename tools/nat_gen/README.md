# nat_gen

Open `Nat` equations `∀ x y : Nat, lhs = rhs := rfl`, where `rhs` is a random
rewrite of `lhs`: offsets (`t + (n+1)` vs `succ (t + n)`), `+ 0`, `0 +`,
commutation, `pred (succ t)`, `(t + n) - n`, `* 1`, notation swaps
(`HAdd` vs `Nat.add`), and off-by-one literals, with literals around the 2^32
and 2^64 boundaries. Python evaluates both sides on a grid (`true` in
`oracle.json`), so a checker that accepts a false equation is unsound. Lean
decides definitional equality under `maxHeartbeats 20000`; refused ones are
exported as `E{i}_f`, added unchecked. Compare checkers against the
`official` verdict from the matrix, not the in-generation one, which may be a
heartbeat timeout.

```bash
python3 tools/nat_gen/gen.py /tmp/nat --pairs 300 --seed 2
python3 tools/scale_gen/run.py /tmp/nat/ex/*.ndjson --timeout 20 --out /tmp/nat.jsonl
```

Results (2026-11-01, seed 2, 206 of 300 exports through all 16 checkers before
the run was stopped for memory): no checker accepted a false equation, and no
divergence from official apart from timeouts and declines (kefir
`resource.reduction_path` on closed `Nat.div` terms, nano-lean-ref's stack
budget).
