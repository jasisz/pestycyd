# Universe-level generator with an arithmetic oracle

`gen.py` builds random pairs of universe levels over `u`, `v`, `w` (zero,
succ, max, imax, parameters), mostly by rewriting one side with
equivalence-preserving and occasionally breaking steps. Each pair becomes

    def Lk.{u,v,w} (x : Sort l1) : Sort l2 := x

which type-checks exactly when the kernel finds `l1` and `l2` equivalent.
The oracle evaluates both levels on every assignment in a small grid, which
decides equivalence for these expressions. Pairs Lean rejects are added
under `Lk_f` with `debug.skipKernelTC`, so every pair is exported.

```sh
python3 tools/level_gen/gen.py /private/tmp/lvl --seed 2000 --pairs 2000 --depth 5
.venv/bin/pestycyd matrix /private/tmp/lvl/ex/*.ndjson
```

`oracle.json` records each pair's equivalence and Lean's verdict. A checker
that accepts an unequal pair is unsound (a universe collapse yields
`False`). An equal pair that Lean rejects, such as `imax u v` against
`imax (imax u v) v`, is an `either` case: Lean's normalization is
incomplete for `imax`.

On 2026-11-01 a run of 2000 pairs gave 637 unequal ones, which no checker
and not Lean accepted, and 287 equal ones that Lean rejects; the latter
became Arena `corner-cases/imax-nested-absorption` (lean-kernel-arena #320, merged).
