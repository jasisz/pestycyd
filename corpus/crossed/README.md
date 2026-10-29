# corpus/crossed — documents merged by tools/cross.py

Each file splices two or more self-contained leanexport documents into one:
index tables are remapped by disjoint offsets, declaration names are resolved
semantically and deduplicated (first document wins). Gives the mutators a
shared environment where divergent feature families co-occur (quot records
next to Acc2 recursors next to instance-chain Nat ops next to eta probes).

| file | parents | notes |
|---|---|---|
| `x-acc2-quot.ndjson` | slice-s2 + slice-s4 | Acc2/Rose mutual inductives + all 4 quot roles in one env |
| `x-pirr-quot.ndjson` | slice-s3 + slice-s4 | proof-irrelevance/Nat env + quot family |
| `x-all-small.ndjson` | s1+s2+s3+s4 | union of the four small slices (102 decls, 25 dups dropped) |
| `x-d1-acc2-quot.ndjson` | slice-d1 + s2 + s4 | 347k-record DecStr prelude + Acc2/Rose + quot (3573 decls). Not committed (16.7 MB); regenerate: `tools/cross.py corpus/crossed/x-d1-acc2-quot.ndjson corpus/real/slice-d1.ndjson corpus/real/slice-s2.ndjson corpus/real/slice-s4.ndjson` |
| `x-eta-family.ndjson` | s2 + eta-pp + unit-eta | PProd structure eta + PUnit/True unit eta in the Rose env |
| `x-acc2-iota-family.ndjson` | s2 + acc2-rec-iota + acc2-prop-iota | Acc2 iota probes (Type + Prop motives) inside their own slice |
| `x-inst-nat.ndjson` | s3 + inst-chain-brecon + nat-ops-small | instance-chain hAdd→instHAdd→Add.add→instAddNat→Nat.add + Nat.brecOn |

All files: unanimous accept on the full matrix (official, paranoid, pestka
old/next/llvm/vm, instrumented nanobruijn, lean4lean, con-leche, con-ron)
except where a deliberately-bad control decl was inherited.
