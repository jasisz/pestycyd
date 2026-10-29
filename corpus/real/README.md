# Real-export slices

Slices of genuine `lean4export` 3.1.0 output (Lean 4.35.0), cut to a closed
dependency set so they replay standalone. They are the base documents for
the hand probes and for `tools/cross.py`.

| file | content |
|---|---|
| `slice-s1.ndjson` | `Nat.add` via `brecOn`, `HAdd`/`Add` instances, `Eq`, `Prod`, `Tree`/`Vec`, proof-irrelevance and K-like probes |
| `slice-s2.ndjson` | `Rose` nested via `List`, `List`/`Eq`/`Two`/`E2T`/`Acc2` machinery |
| `slice-s3.ndjson` | same `Nat` prelude + structure `S3` with eta, proof irrelevance and literal-reduction theorems |
| `slice-s4.ndjson` | `Quot`/`Quot.mk`/`Quot.lift`/`Quot.ind` + `Eq` |
| `slice-d1.ndjson` | 347k records cut from a `Decidable`/`String`/`Char`/`UInt32` export (16.7 MB) |

All slices are accepted unanimously by the full matrix.
