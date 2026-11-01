"""Random universe-level pairs decided by arithmetic, checked by Lean, exported.

Each pair (l1, l2) becomes `def Lk.{u,v,w} (x : Sort l1) : Sort l2 := x`,
which type-checks exactly when the kernel finds `l1` and `l2` equivalent.
The oracle evaluates both levels on every assignment of u, v, w in 0..K-1;
levels built from zero, succ, max, imax and parameters agree everywhere iff
they agree on such a grid for K above their nesting depth (6 by default).
Pairs Lean rejects are added with `debug.skipKernelTC` under the name
`Lk_f`, so each pair is exported either way.  A checker that accepts a pair
the oracle calls unequal is unsound (a universe collapse gives `False`);
one that rejects an equal pair Lean accepts is incomplete.  Equal pairs
that Lean rejects (e.g. `imax u 1` against `max u 1`) are `either`.
"""
import argparse, itertools, json, os, random, subprocess, sys
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
P = ['u', 'v', 'w']
def ev(l, a):
    t = l[0]
    if t == 'z': return 0
    if t == 'p': return a[l[1]]
    if t == 's': return ev(l[1], a) + 1
    x, y = ev(l[1], a), ev(l[2], a)
    if t == 'm': return max(x, y)
    return 0 if y == 0 else max(x, y)          # imax
def equiv(a, b, K=6):
    return all(ev(a, dict(zip(P, xs))) == ev(b, dict(zip(P, xs))) for xs in itertools.product(range(K), repeat=3))
def rnd(d):
    r = random.random()
    if d == 0 or r < 0.25:
        return random.choice([('z',), ('p', 'u'), ('p', 'v'), ('p', 'w'), ('s', ('z',)), ('p', 'u')])
    if r < 0.45: return ('s', rnd(d - 1))
    if r < 0.72: return ('m', rnd(d - 1), rnd(d - 1))
    return ('i', rnd(d - 1), rnd(d - 1))
def rewrite(l):
    """One equivalence-preserving (or occasionally breaking) step somewhere in l."""
    t = l[0]
    if t in ('m', 'i', 's') and random.random() < 0.5:
        k = random.randrange(1, len(l)); ch = list(l); ch[k] = rewrite(l[k]); return tuple(ch)
    c = random.random()
    if t == 'm':
        a, b = l[1], l[2]
        if c < 0.2: return ('m', b, a)
        if c < 0.3 and b[0] == 'm': return ('m', ('m', a, b[1]), b[2])
        if c < 0.4: return ('m', l, a)                          # max (max a b) a
        if c < 0.5 and a[0] == 's' and b[0] == 's': return ('s', ('m', a[1], b[1]))
    if t == 's' and l[1][0] == 'm' and c < 0.4:
        return ('m', ('s', l[1][1]), ('s', l[1][2]))
    if t == 'i':
        a, b = l[1], l[2]
        if c < 0.25 and b[0] == 's': return ('m', a, b)       # imax a (succ b) = max a (succ b)
        if c < 0.4 and b[0] == 'i': return ('i', ('m', a, b[1]), b[2])  # imax a (imax b c) = imax (max a b) c
        if c < 0.5: return ('i', l, b)                          # imax (imax a b) b
        if c < 0.6 and a == b: return a
        if c < 0.7: return ('i', b, a)                          # usually breaks
    if c < 0.08: return ('s', l)                                # breaks
    if c < 0.12: return ('m', l, ('z',))
    if c < 0.16: return ('i', ('z',), l)                        # imax 0 l = l
    if c < 0.2: return ('i', l, l)                              # imax l l = l
    if c < 0.24: return ('m', l, rnd(1))                        # may break
    return l
def lean(l):
    t = l[0]
    if t == 'z': return 'Level.zero'
    if t == 'p': return f'(Level.param `{l[1]})'
    if t == 's': return f'(Level.succ {lean(l[1])})'
    return f'({"Level.max" if t == "m" else "Level.imax"} {lean(l[1])} {lean(l[2])})'
LEAN_PRELUDE = '''import Lean
open Lean Elab Command
set_option Elab.async false

def tryDef (n : Name) (l1 l2 : Level) : CoreM Bool := do
  let ty := Expr.forallE `x (.sort l1) (.sort l2) .default
  let v : DefinitionVal := { name := n, levelParams := [`u, `v, `w], type := ty, value := .lam `x (.sort l1) (.bvar 0) .default, hints := .abbrev, safety := .safe }
  let before := (← get).messages.toList.length
  let ok ← try addDecl (.defnDecl v); pure true catch _ => pure false
  let ok := ok && (← get).messages.toList.length == before && (← getEnv).contains n
  if !ok then
    modify fun s => { s with messages := {} }
    withOptions (debug.skipKernelTC.set · true) <|
      addDecl (.defnDecl { v with name := n.appendAfter "_f" })
  return ok
'''


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("output", type=Path, help="new output directory")
    ap.add_argument("--seed", type=int, default=5)
    ap.add_argument("--pairs", type=int, default=400)
    ap.add_argument("--depth", type=int, default=4)
    ap.add_argument("--workers", type=int, default=4)
    ap.add_argument("--lean", default=str(Path.home() / ".elan/toolchains/leanprover--lean4---v4.35.0/bin/lean"))
    a = ap.parse_args()
    random.seed(a.seed)
    pairs = []
    while len(pairs) < a.pairs:
        x = rnd(random.randint(1, a.depth)); y = x
        for _ in range(random.randint(1, 6)):
            y = rewrite(y)
        if x != y:
            pairs.append((x, y, equiv(x, y, max(6, a.depth + 3))))
    a.output.mkdir(parents=True, exist_ok=False)
    lines = [LEAN_PRELUDE]
    for i, (x, y, _) in enumerate(pairs):
        lines += ["run_cmd liftTermElabM do", f"  let r ← tryDef `L{i} {lean(x)} {lean(y)}",
                  f'  IO.FS.withFile "lean.txt" .append fun h => h.putStrLn s!"L{i} {{r}}"']
    (a.output / "Lv.lean").write_text("\n".join(lines) + "\n")
    prefix = subprocess.check_output([a.lean, "--print-prefix"], text=True).strip()
    env = {**os.environ, "LEAN_PATH": f"{a.output}:{prefix}/lib/lean"}
    subprocess.run([a.lean, "-o", "Lv.olean", "Lv.lean"], cwd=a.output, env=env, check=True)
    verdicts = dict(l.split() for l in (a.output / "lean.txt").read_text().splitlines())
    (a.output / "ex").mkdir()
    def export(i: int) -> None:
        name = f"L{i}" if verdicts[f"L{i}"] == "true" else f"L{i}_f"
        out = subprocess.run([str(Path(prefix) / "bin/leanexport"), "Lv", "--", name],
                             cwd=a.output, env=env, capture_output=True, text=True, check=True).stdout
        (a.output / "ex" / f"{name}.ndjson").write_text(out)
    with ThreadPoolExecutor(a.workers) as pool:
        list(pool.map(export, range(len(pairs))))
    oracle = [{"name": f"L{i}", "a": repr(x), "b": repr(y), "equiv": eq,
               "lean": verdicts[f"L{i}"] == "true"} for i, (x, y, eq) in enumerate(pairs)]
    (a.output / "oracle.json").write_text(json.dumps(oracle, indent=1))
    unsound = [o["name"] for o in oracle if o["lean"] and not o["equiv"]]
    print(json.dumps({"pairs": len(pairs), "equal": sum(o["equiv"] for o in oracle),
                      "lean_accepts": sum(o["lean"] for o in oracle),
                      "lean_accepts_unequal": unsound}, indent=1))


if __name__ == "__main__":
    main()
