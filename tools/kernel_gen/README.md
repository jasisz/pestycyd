# Kernel-level inductive generator

`GenInd.lean` builds random inductive declarations as Lean expressions and
passes each block through ordinary `addDecl`. Accepted types, constructors,
and recursors feed `Gen.lean`, which generates more checked definitions and
theorems. It also creates one near-miss declaration per accepted term; those
are added with `debug.skipKernelTC` solely to produce reject controls.
Blocks include mutual types, Bool indices that may depend on a constructor
field, polymorphic sorts, and recursive fields under `List`, `Option`,
`Prod`, or `Array`.

`--rec-terms` adds theorems that apply a generated recursor to a closed
constructor term. Their motives return `Nat`; minor premises either return
zero or combine a constructor's Nat fields and induction results. Lean checks
each theorem by reflexivity after reducing the application to a numeral.

`--hide N` hides N% of constructor fields (and recursive occurrences inside
containers) behind a vacuous beta, a vacuous `let`, or `@id (Sort l)`. The
elaborator never writes these, but the kernel reduces through them. Lean's
nested-occurrence lookup is still syntactic, so `List ((fun _ => T) true)`
and `List T` become two auxiliary types. Half as often, a `Bool` or `Nat` field
becomes `(fun X => Nat) T`, `(fun X => Nat) (T → Nat)` or the same with an
unused `let`: the block occurs only where weak head normalisation discards
it, which Lean's positivity check accepts
(`corpus/leads/kefir-vanishing-occurrence-*.ndjson`). This is how
`corpus/leads/sokonanoda-nested-redex-merge.ndjson` was found (seed 913,
`--blocks 300 --rec-terms 1200 --hide 50`).

`--rich` gives polymorphic blocks two universe parameters with sorts such as
`max u v + 1`, `imax v (u + 1)` or `max 1 (imax u v)`, parameters in either
universe, and `Nat` indices (literal targets and `Vec`-style constructors
`n → T n → T (n + 1)`) beside `Bool` ones. Three seeds of 400 blocks and 2500
recursor attempts (2026-11-01, 1946 exports) found only known classes.

The runner compiles the Lean modules, exports each selected declaration with
`leanexport`, and writes a `summary.json`. It uses the local Lean 4.35.0
toolchain by default when present; pass `--lean` for another installation.

```sh
python3 tools/kernel_gen/run.py /private/tmp/indgen-41 \
  --seed 41 --blocks 40 --terms 150 --rec-terms 100 --limit 10
.venv/bin/pestycyd matrix /private/tmp/indgen-41/inductive/*.ndjson \
  /private/tmp/indgen-41/good/*.ndjson \
  /private/tmp/indgen-41/bad/*.ndjson \
  /private/tmp/indgen-41/rec/*.ndjson
```

The output directory must be new. Omit `--limit` to export every accepted
inductive type, term, recursor theorem, and reject control. `build/` retains
the `.lean`, `.olean`, and name lists so any case can be regenerated or
inspected.

A seed 809 run with 300 block attempts and 1200 recursor attempts produced
451 checked recursor theorems. Among 150 exported theorems, 64 reduced to a
positive numeral (maximum 241). The 16-checker matrix found only 27 instances
of nanobruijn#2 and one kefir resource limit on a roughly 500 KB export.
On those 150 recursor theorems, 1600 mutations of inductive metadata and
recursor rules with the final goal protected produced no untriaged finding.
