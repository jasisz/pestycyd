# Hand probes

Closed experiments kept as evidence for statements in the other READMEs.
They are neither `good` seeds (several are deliberately rejected) nor open
`leads`. Most were written to `/tmp` during the 2026-10-29 sessions and
rescued here.

| path | what it shows |
|---|---|
| `acc2-iota-neg.ndjson` | Unanimously-rejected control for `good/acc2-rec-iota` (`acc2_iota_neg`). |
| `qred-{bad,ctorlift,lp,tswap}.ndjson` | `Quot.lift` reduction on documents with forged `quot` metadata; companions of `leads/quot-qred-honest`. |
| `malformed/*.ndjson` | Parse-level probes: `natVal` `"-5"`/`"abc"`/`""`/500-digit/1001-digit, `sort` index `-1`/`999999`, `bvar` `999999`, `strVal` NUL/unicode — unanimous rejects (parse or `type expected`); a 500-digit natVal parses fine on all checkers. |
| `level-diff/level-diff-*.ndjson` | The 613-file `imax`/`max` level sweep behind `leads/pestka-imax-literal`: official and Pestka agree on every probe; lean4lean over-accepts 28. |
| `d1-tails/*.tail` | Declarations appended to `real/slice-d1.ndjson`. Not standalone documents; rebuild with `cat corpus/real/slice-d1.ndjson corpus/probes/d1-tails/X.tail > X.ndjson`. |

`d1-tails`:

- `opaque-probe` / `def-probe` — `Eq (String.Internal.append "a" "b") "ab"` by `rfl`: unanimous reject on the opaque, unanimous accept on the `def` `String.append`.
- `bignum` — `Nat.pow 2 64/100`, `Nat.mul 2^32·2^32`, `add`/`sub`/`div`/`mod`/`pred`/`shiftRight` at the u64 boundary, 10^40 products, `gcd` — all unanimous vs `natVal` decimal literals (12 probes + rejected control).
- `strchar` — unicode `strVal`, `String.append`/`length` (length counts chars), `UInt32.ofNat` wraparound, `Nat.land`/`lor` on bignums.
- `charclamp` — `Char.ofNat` *clamps* invalid scalars to `'\x00'` (surrogates 0xD800–0xDFFF, `≥0x110000`, bignums) while 0xE000 is preserved — unanimous across all checkers incl. con-*.

Lost: the `decstr-probes*` batch (~48 fast-path-vs-definition probes on
`Decidable`/`String`/`Char`/`UInt32`/`Nat` ops, unanimous accept on all 9
kernels incl. `leanchecker-paranoid`) did not survive in `/tmp`. Its base
export `DecStr.ndjson` (330 MB) is not stored either; `real/slice-d1` is the
347k-record slice cut from it.
