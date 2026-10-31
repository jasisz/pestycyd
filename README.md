# Pestycyd

**Pest control for Lean kernels.**

*Pestycyd* is Polish for **pesticide**. The name is deliberate: the tool grew
out of Pestka's soundness harness and now hunts bugs across every kernel, not
only Pestka.

Pestycyd runs `lean4export` NDJSON inputs through independent Lean kernel
implementations, creates structure-aware mutations, records reproducible
findings, grows an instrumentation-guided corpus, and minimizes cases. It is
checker-neutral: Pestka, the official kernel, Lean4Lean, Nanoda, Sokonanoda,
Kefir, MathGraph, Tenet and the `con-*` checkers are ordinary configured
targets.

The important distinction is explicit throughout the tool:

- `guaranteed-reject`: the mutation is invalid by construction; an acceptance
  is a soundness finding;
- `guaranteed-accept`: the transformation preserves validity; a rejection is
  a completeness finding;
- `differential`: disagreement is a lead, not proof that any checker is wrong.

An exit code is never a verdict on its own when a target requires verdict
output. In particular, exit code 1 without a `rejected:` line is a runner
error, not a rejection.

## Quick start

```bash
uv sync --locked
uv run pestycyd --config pestycyd.toml doctor
uv run pestycyd --config pestycyd.toml matrix corpus/good --report before.json
# after rebuilding a checker: which verdicts moved?
uv run pestycyd --config pestycyd.toml matrix corpus/good --baseline before.json
uv run pestycyd renumber hand-edited.ndjson dense.ndjson
uv run pestycyd --config pestycyd.toml campaigns
uv run pestycyd --config pestycyd.toml hunt corpus/good \
  --campaign closedness --campaign metadata-boundaries \
  --iterations 1000 --max-depth 3
uv run pestycyd --config pestycyd.toml hunt corpus/regressions \
  --seed-policy consensus --iterations 1000
uv run pestycyd --config pestycyd.toml minimize finding.ndjson minimal.ndjson \
  --expect official=reject --expect nanoda=accept
uv run pestycyd --config pestycyd.toml reduce finding.ndjson minimal.ndjson \
  --expect official=reject --expect nanoda=accept
uv run pestycyd --config pestycyd.toml findings --report clusters.json
uv run pestycyd --config pestycyd.toml bench bench/scenarios.toml \
  --report bench-report.json
```

`uv.lock` is committed; normal development and CI use `uv run --locked ...`.
`minimize` preserves lean4export's continuous name, level, and expression
back-reference tables by default, so a semantic disagreement cannot collapse
into an unrelated parser failure. Use `--allow-malformed` only when the parser
failure itself is the bug being reduced.

## Configuration

Copy `pestycyd.example.toml` and use argv arrays: commands never pass through
a shell. Paths and working directories are relative to the configuration
file. `{file}` must occur in either the command or an environment value. The
example contains every checker used during the original Pestka audit; only the
two native Pestka cores are enabled by default. A disabled target can still be
selected explicitly with `--kernel NAME`.

```toml
version = 1

[defaults]
timeout = 20.0
state = ".pestycyd"

[kernels.pestka]
command = ["../.build/target/release/main", "{file}", "1", "old"]
verdict = "required"

[kernels.kefir]
command = ["kefir", "--axiom-policy=allow-all-declared-axioms"]
env = { IN = "{file}" }
verdict = "none"
enabled = false

[kernels.tenet]
command = ["tenet", "check", "{file}", "--quiet"]
verdict = "none"

[kernels.tenet.exit_codes]
accept = 0
reject = 1
decline = 4
```

`required` means the process must print a recognized verdict matching its
exit code. `optional` falls back to the conventional 0/1/2 mapping when no
verdict is printed. `none` always uses the exit code. `exit_codes` handles
checkers such as Tenet whose explicit decline is not code 2.

## Instrumentation and the fuzzing loop

Instrumentation is optional per kernel. `{run_dir}` names a fresh private
directory for one execution and can be used in command arguments and
environment variables. A source-instrumented checker can emit stable feature
IDs directly:

```toml
[kernels.pestka-instrumented]
command = ["../pestka-cov", "{file}", "1", "old"]
verdict = "required"
env = { PESTYCYD_TRACE = "{run_dir}/trace" }

[kernels.pestka-instrumented.feedback]
format = "lines"
path = "{run_dir}/trace"
required = true
```

Each non-empty line is one feature; semantic points such as
`decl.safe.closed`, `whnf.delta`, or `recursor.rule.checked` are ideal. For
compiler or sanitizer coverage use `format = "bitmap"`: every non-zero byte
offset becomes a feature and counter values are bucketed. Large native profiles
can use `format = "bitmap-chunks"`; Pestycyd hashes non-zero 64-byte chunks,
retaining change feedback without allocating a feature string for every
metadata byte. The first 128 bytes are treated as a volatile native-profile
header and skipped. Instead of `path`,
`command = [...]` may run a postprocessor (for example `llvm-profdata` plus
`llvm-cov`); its stdout is interpreted in the selected format.

An LLVM-instrumented Pestka needs no manual source edits. The included adapter
builds it separately from the release binary:

```bash
adapters/pestka/build-coverage /path/to/pestka
```

The adapter uses `AVER` when set (and otherwise `aver` from PATH). To
instrument an already generated, known-good `.build/Cargo.toml` without
running Aver again:

```bash
PESTYCYD_REUSE_GENERATED=1 adapters/pestka/build-coverage /path/to/pestka
```

Point `LLVM_PROFILE_FILE` at the run directory and use the included converter:

```toml
[kernels.pestka-llvm]
command = ["../.build-pestycyd/target/release/main", "{file}", "1", "old"]
verdict = "required"
env = { LLVM_PROFILE_FILE = "{run_dir}/pestycyd-%p-%m.profraw" }

[kernels.pestka-llvm.feedback]
format = "lines"
command = [
  "pestycyd-llvm-feedback",
  "../.build-pestycyd/target/release/main",
  "{run_dir}/*.profraw",
  "--source-root", "../.build-pestycyd/generated",
  "--only-source-root",
]
required = true
```

The converter discovers the matching `llvm-profdata` and `llvm-cov` from PATH
or Rust's `llvm-tools-preview` component. LLVM export is deliberately the
high-fidelity, slower mode; a native bitmap or semantic line trace is the hot
loop mode for long campaigns.

`hunt` seeds the known feature set with accepted inputs. A mutant that adds
features is stored under `.pestycyd/corpus/` and, up to `--max-depth`, becomes
a new mutation parent. `--max-children` bounds frontier growth. A disagreement,
invalid acceptance, crash, timeout, or process error is stored independently
under `.pestycyd/findings/`. Thus code coverage guides exploration but never
becomes a soundness oracle.

By default, every selected kernel must accept a seed. `--seed-policy consensus`
also admits seeds that every kernel rejects, which makes repaired historical
reproductions useful as coverage-guided starting points. `--seed-policy any`
admits non-fatal baseline disagreement as well; `--seed-policy all` also admits
crashes and runner errors when the purpose of mutation is to repair an almost
working historical input. `--behavior-feedback` lets normalized outcome changes
grow a release-only corpus when no instrumented checker is available.

`--protect-final-goal` freezes the last theorem declaration and the expression
graph of its type while mutations continue attacking the environment it relies
on. Initial mutations are scheduled round-robin across seeds, so one large
export cannot starve smaller cases. `--semantic-only` keeps crash and timeout
noise out of findings without removing it from search feedback.

`--protect-prelude` freezes the constants the official kernel trusts by name
(`Nat.add` and the other literal fast paths, `String`, `Char.ofNat`, `Quot`,
...) together with everything they reach, including the declarations of
constants they use. Lean's threat model assumes the official prelude: a
`False` obtained by redefining `Nat.add` is "not a bug"
([lean4#15908](https://github.com/leanprover/lean4/issues/15908), the
[kernel bug hunt guide](https://hackmd.io/Tu2Z97xHSQilI7b91HQfAw)), so a hunt
aimed at reportable findings should never mutate that cone. It does not
detect a seed whose prelude is already non-standard.

For a soundness hunt, exact outcome expectations keep `reject`/`decline`
differences from becoming findings:

```bash
uv run pestycyd --config pestycyd.toml hunt corpus/ \
  --finding-expect official=reject --finding-expect target=accept
```

This filter changes only which inputs are recorded as findings. Coverage and
behavior feedback still grow the search through other outcomes.
When evolving known mismatches or near-misses, add
`--finding-require-seed-change` to suppress candidates whose original seed
already had the requested outcome vector. The seed result remains recorded in
the sidecar as `seed_matched_finding_expectations`.
`--feedback-depth-first` runs children of a coverage- or behavior-expanding
input immediately, which is useful for multi-step escalation from a near-miss;
the default breadth-first schedule remains better for broad corpus discovery.
`--budget-seconds` stops the loop after a wall-time budget, which keeps large
campaigns inside a fixed test window.

The oracle and the seed policy interact. `guaranteed-accept` proves the child
correct only when the parent was correct, so it is sound exactly under the
default `accepted` policy; under any other policy Pestycyd silently downgrades
those mutations to `differential` instead of manufacturing findings from
rejections that predate the mutation. Chains composed entirely of
validity-preserving steps keep the stronger oracle at depth two and beyond.

Two name-sensitive mechanisms also constrain the metamorphic campaigns.
Kernel-derived names make declaration order semantic: processing an
inductive checks `<ind>.rec` and generates `_nested.*` against the
environment as it goes, and the official kernel — like Lean itself —
rejects a block whose recursor name is already taken, so
`declaration-reordering` only swaps plain declarations (no `inductive` or
`quot` partners, no `_nested`/`.rec`-shaped names). And checkers key
native reduction on trusted names (`Nat.add`, `String.append`, ...), so
`metamorphic-rename` never renames a declaration rooted at such a family:
the rewrite would change what the checker trusts, not how the proof is
presented.

## Built-in corpus and generators

`corpus/good/` contains small official-kernel-accepted mutation seeds.
`corpus/regressions/` contains confirmed historical bugs and negative
escalation attempts. `corpus/leads/` contains composition material that is not
itself a soundness claim. Their READMEs link every filed upstream issue and
mark cases that were never filed.

The large boundary families are generated on demand:

```bash
uv run pestycyd generate deep-binder 16382 /tmp/deep.ndjson
uv run pestycyd generate con-k-params 10000 /tmp/WideK.lean
```

`generate inductives` makes new seeds rather than new edits of old ones. It
draws random inductive families: parameters in `Type`/`Prop`, `Bool`/`Unit`
indices, the sorts `Prop`, `Type`, `Type u` and `Sort (max 1 u)`, and plain,
recursive, reflexive (`Bool → T`) and `List`-nested fields. Each family gets
a closed term and a theorem `@T.rec … term = N := rfl`. Every minor premise
returns its constructor number plus its recursive results, and Python
computes the same fold, so `N` is known without asking any checker.
Lean filters for validity: families it refuses (positivity, universe
constraints) are dropped and the rest are exported with `leanexport`.
Propositional families without large elimination are used with a
`True`-valued motive. For each family with a numeric result,
`rejects/` holds the same export with `N` off by one, which every checker
must refuse:

```bash
B=$(dirname $(elan which lean))
uv run pestycyd generate inductives /tmp/gen --count 200 --seed 1 \
  --lean $B/lean --leanexport $B/leanexport
uv run pestycyd matrix /tmp/gen/*.ndjson /tmp/gen/rejects/*.ndjson
uv run pestycyd hunt --campaign single-fault --campaign inductive-structure /tmp/gen
```

`generate nested` goes where hand-written recursor applications cannot:
mutual blocks of one to three types, optionally `Bool`-indexed, whose fields
nest the block up to three containers deep through `List`, `Option`, `×`,
`Array` and four containers declared alongside (`Rose`, itself nested;
`Pair2`, a structure over `List`; `Vec`, indexed; `Wrap`, reflexive). The
theorem is `Nat.add 1000000 (sizeOf term) = 1000000 + N := rfl`: Lean
derives `SizeOf` through the block's recursors, one motive per nested
auxiliary type, so a checker must get every auxiliary recursor right. `N`
comes from the elaborator's `#reduce`, and Lean's kernel checks the theorem
before export. A second theorem `fold` evaluates a mutual group of
structurally recursive functions, one per block type and per nested
container, so the check also runs through `brecOn`/`below`; about a third of
the blocks live in `Type u`, making both theorems universe-polymorphic.
The same flags apply; `rejects/` holds one off-by-one copy per theorem. Its first run found
[nanobruijn#2](https://github.com/nomeata/nanobruijn/issues/2): a valid
mutual block with one non-recursive member panics nanobruijn.

The structural campaigns from Pestka's `arena-candidate` branch were ported as
`expression-structure`, `declaration-structure`, and `inductive-structure`.
`expression-structure` truncates at the affected declaration for isolated
diagnosis; `expression-structure-full` preserves downstream declarations and
is the end-to-end variant for escalating old `False` reproductions.
They remain `differential`; only closedness and duplicate checked universe
parameters currently carry the stronger `guaranteed-reject` oracle.

The stateful campaigns attack relationships that single-field fuzzers miss:
`declaration-replay` and `declaration-shadow-copy` exercise duplicate environment
entries, `inductive-block-crosswire` transplants scope-compatible recursor
semantics, and `intern-table-shadowing` inserts a second expression under an
already-used intern ID immediately before a declaration consumes it.
`recursor-rule-permutations` also exercises serialized recursor fields. The
checked-in `prop-recursor-derived-field-swap.ndjson` is a negative control, not
a soundness finding: those fields are derived from the inductive declaration,
so a checker may safely derive and ignore them.

The metamorphic campaigns are the first built-in users of the
`guaranteed-accept` oracle. Each applies a validity-preserving rewrite —
`metamorphic-beta` wraps a declaration value in an identity application,
`metamorphic-let` in a redundant `let`, `metamorphic-eta` expands a Pi-typed
value to `fun x => v x`, `metamorphic-rename` renames a declaration
consistently to a fresh name, `expression-unsharing` rebuilds a shared value
DAG as a private copy, and `declaration-reordering` moves a declaration past
an independent neighbour — so any rejection is a completeness finding. The
rewrites are real graph transformations: inserted expression records force a
dense renumbering of the whole export, which the `pestycyd.rewrite` core
performs while rewriting every back-reference.

## Reduction, clustering, and escalation detection

`minimize` deletes lines; `reduce` deletes *records*. On every trial, `reduce`
garbage-collects records unreachable from the declarations and renumbers the
name, level, and expression tables densely, so a deletion from the middle of a
table no longer collapses the case into an unrelated parser failure. Inputs
that rely on duplicate table identifiers — intern-table shadowing findings —
fall back to plain line minimization, because renumbering would erase the
defect under study:

```bash
uv run pestycyd --config pestycyd.toml reduce finding.ndjson minimal.ndjson \
  --expect official=reject --expect nanoda=accept
```

The same canonicalization powers `findings`, which answers "how many distinct
defects did this hunt produce?" instead of "how many files?". Findings whose
documents canonicalize to identical bytes are the same case in a different
presentation and are reported as one cluster:

```bash
uv run pestycyd --config pestycyd.toml findings --report clusters.json
```

Both commands also flag `∀ P : Prop, P` — the canonical escalation target —
detected structurally: the final theorem's goal (through level-free
definition unfolding) is either that binder shape or a constant of an
inductive with zero constructors in `Prop`, in an axiom-free, safe-fragment
document. The check is immune to name shadowing by construction.

## Triage of known divergences

Most disagreements between checkers are long understood: a checker derives a
field instead of reading it, runs out of a declared budget, rejects by
panicking, or declines a feature by design. `src/pestycyd/triage.toml` records
those classes as rules, each with the reason it is not a bug:

```toml
[[rule]]
id = "con-derived-recursor-rules"
why = "con-* derive recursor rules and ignore serialized rules[]"
kernels = ["con-*"]                          # fnmatch on kernel names
status = ["accept"]
expected = ["reject"]                        # optional
sites = ["inductive.recs.rules*"]            # optional
output = "regex on the checker's output"     # optional
reference = "regex on official's output"     # optional
campaigns = ["..."]                          # optional, fnmatch
labels = ["..."]                             # optional, fnmatch
```

Every finding gets an expected verdict: the oracle's, else official's, else
the plurality's. A checker *deviates* when its status differs, and a rule
*explains* it when all given fields match. `sites` names where the mutation
lands: the declaration field it edits, or for an edited table record every
declaration field that reaches it. "Only a recursor rule changed" thus differs
from "a definition changed". A finding is *known* when every deviation is
explained, so several known classes may combine on one input.

Hunts tag known findings `[known: …]`, store the triage in the sidecar, and
exit non-zero only for untriaged findings. `findings` lists untriaged clusters
and the deviating checkers that no rule explains, and rolls the rest up by
class (`--all` lists them too). On the project's own archive of about 3000
findings the built-in rules explain 95%; the rest are the cases worth a human.
Add project-specific rules with `triage = ["my-triage.toml"]` under
`[defaults]`; those files are tried before the built-in ones. Keep a rule
narrow (`sites`, `output`, `reference`), because a broad one hides bugs.

## Per-declaration verdicts

Kernels answer once per document, so a disagreement says *that* checkers
split, not *where*. `locate` names the declaration at which each refusing
kernel first refuses. Checkers replay declarations in order and stop at the
first refusal, so a verdict is monotone in the document prefix and a binary
search over prefixes finds the boundary in `O(log n)` runs per kernel:

```bash
uv run pestycyd --config pestycyd.toml locate finding.ndjson \
  --output cut.ndjson --report locate.json
```

```
finding.ndjson: 32 declarations, 28 kernel runs
  nanoda     reject at #13 def Nat.add._f: Invalid projection: PProd != Nat
  official   reject at #13 def Nat.add._f: (kernel) invalid projection
```

A prefix ends with its last declaration; table records belong to the
declaration that follows them, and the empty prefix keeps only the header,
so a kernel refusing before any declaration is reported as such. Prefixes
are cut, not renumbered, which keeps re-bound table identifiers intact.
`--output` writes the document cut after the earliest refused declaration —
the part a report needs. Each line quotes the kernel's reason: the message
of a Rust panic, otherwise the first line that reads like a refusal.

## Mutation score

The discovery benchmark replays bugs somebody already found. `efficacy`
measures the search on bugs nobody has looked for: it seeds defects into a
real checker and counts how many the hunt catches. `tools/mutants/` holds
the defect specs — each mutant removes or weakens one check by exact text
replacement — and a builder that compiles every variant plus the unmodified
`pristine` control:

```bash
uv run python tools/mutants/build.py tools/mutants/nanobruijn.toml \
  /path/to/nanobruijn .pestycyd/mutants/nanobruijn
uv run pestycyd --config pestycyd.toml efficacy bench/efficacy-nanobruijn.toml \
  --report efficacy.json
```

A mutant is *killed* by an input on which it disagrees with the reference
kernel while the pristine build still agrees, so divergences the checker
already had never count. Each mutant first meets the seeds alone — what the
corpus already catches — and, if it survives, a budgeted hunt that stops at
the first kill; the summary separates the two. Mutants with a `history`
restore a defect that once shipped upstream.

## Discovery benchmark

`bench/scenarios.toml` pins historical defect families without handing the
tool the reproduction. Each scenario selects kernels from the active config, a
correct seed, campaigns, a fixed budget, and — for differential scenarios —
the outcome vector that identifies the bug; a `guaranteed-accept` scenario
pins no vector and lets the oracle define the finding. The report records
whether the hunt reached its target, after how many attempts, how many
canonical clusters it produced, and whether any finding closed the canonical
false theorem:

```bash
uv run pestycyd --config pestycyd.toml bench bench/scenarios.toml \
  --report bench-report.json
```

Pinning checker versions is deliberately outside the scenario file: kernels
come from the config, so the same scenarios measure a suspect build and its
repaired successor. This is how changes to Pestycyd itself — a new campaign,
scheduler, or feedback scheme — earn their keep: run the benchmark before and
after and compare `found`, `first_finding.attempt`, and the cluster count.

## Findings

`hunt` stores each novel interesting input under its SHA-256:

```text
.pestycyd/
  runs.jsonl
  corpus/
    2ac4....ndjson
    2ac4....json
  findings/
    8dc1....ndjson
    8dc1....json
```

The sidecar records the seed, campaign, exact mutation, kernel configuration,
outcomes, timing, output tail, and executable fingerprints where available.
Re-running the same content updates neither artifact, so parallel or repeated
campaigns naturally deduplicate.

## Development

```bash
uv run --locked python -m unittest discover -s tests -v
```

