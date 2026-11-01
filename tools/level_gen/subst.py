"""Universe substitution under an arithmetic oracle.

For each case a polymorphic `Gk.{u,v} (x : Sort l1) : Sort l2 := x` (with
l1 ≡ l2 by construction) is used as `Hk.{u,v,w} (y : Sort m1) : Sort m2 :=
Gk.{a,b} y`, where a, b are random levels over u, v, w.  `Hk` type-checks
iff m1 ≡ l1[a,b] and m2 ≡ l2[a,b]; m1, m2 are random rewrites of the
substituted levels, so some are equivalent and some are near misses.
Several cases share one declaration body to stress per-instantiation caches:
`Hk` applies `Gk` at two different instantiations in a row.
"""
import argparse, itertools, json, os, random, subprocess, sys
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
sys.path.insert(0, str(Path(__file__).parent))
from gen import rnd, rewrite, lean, ev, P

def subst(l, s):
    t = l[0]
    if t == 'p': return s.get(l[1], l)
    if t == 'z': return l
    if t == 's': return ('s', subst(l[1], s))
    return (t, subst(l[1], s), subst(l[2], s))

def equiv(a, b, K=5):
    return all(ev(a, dict(zip(P, xs))) == ev(b, dict(zip(P, xs))) for xs in itertools.product(range(K), repeat=3))

def only_uv(d):
    while True:
        l = rnd(d)
        if 'w' not in repr(l): return l

PRELUDE = '''import Lean
open Lean Elab Command
set_option Elab.async false

/-- Add G with l2; if Lean's incomplete level check refuses an equivalent l2, use l1 for both
(the oracle is semantic, so substituted results stay equivalent). -/
def addG (n : Name) (l1 l2 : Level) : CoreM Unit := do
  let mk (l2 : Level) (n := n) : DefinitionVal := { name := n, levelParams := [`u, `v], type := .forallE `x (.sort l1) (.sort l2) .default, value := .lam `x (.sort l1) (.bvar 0) .default, hints := .abbrev, safety := .safe }
  let before := (← get).messages.toList.length
  let probe := n.appendAfter "_probe"
  let ok ← try addDecl (.defnDecl (mk l2 probe)); pure true catch _ => pure false
  let ok := ok && (← get).messages.toList.length == before
  modify fun s => { s with messages := {} }
  addDecl (.defnDecl (mk (if ok then l2 else l1)))

/-- H (y : Sort m1) : Sort m2 := G.{c,d} (G.{a,b} y)  (inner then outer instantiation). -/
def tryH (n g : Name) (a b c d m1 m2 : Level) : CoreM Bool := do
  let inner := mkApp (mkConst g [a, b]) (.bvar 0)
  let body := mkApp (mkConst g [c, d]) inner
  let v : DefinitionVal := { name := n, levelParams := [`u, `v, `w], type := .forallE `y (.sort m1) (.sort m2) .default, value := .lam `y (.sort m1) body .default, hints := .abbrev, safety := .safe }
  let before := (← get).messages.toList.length
  let ok ← try addDecl (.defnDecl v); pure true catch _ => pure false
  let ok := ok && (← get).messages.toList.length == before && (← getEnv).contains n
  if !ok then
    modify fun s => { s with messages := {} }
    withOptions (debug.skipKernelTC.set · true) <| addDecl (.defnDecl { v with name := n.appendAfter "_f" })
  return ok
'''

def main():
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument('output', type=Path); ap.add_argument('--seed', type=int, default=1)
    ap.add_argument('--cases', type=int, default=300); ap.add_argument('--workers', type=int, default=6)
    ap.add_argument('--lean', default=str(Path.home() / '.elan/toolchains/leanprover--lean4---v4.35.0/bin/lean'))
    a = ap.parse_args(); random.seed(a.seed)
    cases = []
    while len(cases) < a.cases:
        l1 = only_uv(random.randint(1, 3)); l2 = l1
        for _ in range(random.randint(0, 3)): l2 = rewrite(l2)
        if 'w' in repr(l2) or not equiv(l1, l2): continue          # G must be valid
        A, B, C, D = (rnd(random.randint(0, 2)) for _ in range(4))
        # G.{a,b} : Sort l1[a,b] -> Sort l2[a,b]; G.{c,d} needs its input l1[c,d] ≡ l2[a,b]
        mid_in, mid_out = subst(l1, {'u': A, 'v': B}), subst(l2, {'u': A, 'v': B})
        out_in, out_out = subst(l1, {'u': C, 'v': D}), subst(l2, {'u': C, 'v': D})
        if not equiv(mid_out, out_in):
            if random.random() < 0.7: continue                     # keep mostly composable chains
        m1, m2 = mid_in, out_out
        for _ in range(random.randint(0, 3)): m1 = rewrite(m1)
        for _ in range(random.randint(0, 3)): m2 = rewrite(m2)
        valid = equiv(m1, mid_in) and equiv(mid_out, out_in) and equiv(m2, out_out)
        cases.append((l1, l2, A, B, C, D, m1, m2, valid))
    a.output.mkdir(parents=True, exist_ok=False)
    lines = [PRELUDE]
    for i, (l1, l2, A, B, C, D, m1, m2, _) in enumerate(cases):
        lines += [f'run_cmd liftTermElabM do addG `G{i} {lean(l1)} {lean(l2)}',
                  'run_cmd liftTermElabM do',
                  f'  let r ← tryH `H{i} `G{i} {lean(A)} {lean(B)} {lean(C)} {lean(D)} {lean(m1)} {lean(m2)}',
                  f'  IO.FS.withFile "lean.txt" .append fun h => h.putStrLn s!"H{i} {{r}}"']
    (a.output / 'S.lean').write_text('\n'.join(lines) + '\n')
    prefix = subprocess.check_output([a.lean, '--print-prefix'], text=True).strip()
    env = {**os.environ, 'LEAN_PATH': f'{a.output}:{prefix}/lib/lean'}
    subprocess.run([a.lean, '-o', 'S.olean', 'S.lean'], cwd=a.output, env=env, check=True)
    verdicts = dict(l.split() for l in (a.output / 'lean.txt').read_text().splitlines())
    (a.output / 'ex').mkdir()
    def export(i):
        n = f'H{i}' if verdicts[f'H{i}'] == 'true' else f'H{i}_f'
        out = subprocess.run([str(Path(prefix) / 'bin/leanexport'), 'S', '--', n], cwd=a.output, env=env, capture_output=True, text=True, check=True).stdout
        (a.output / 'ex' / f'{n}.ndjson').write_text(out)
    with ThreadPoolExecutor(a.workers) as pool: list(pool.map(export, range(len(cases))))
    oracle = [{'name': f'H{i}', 'valid': c[-1], 'lean': verdicts[f'H{i}'] == 'true', 'case': repr(c[:-1])} for i, c in enumerate(cases)]
    (a.output / 'oracle.json').write_text(json.dumps(oracle, indent=1))
    print(json.dumps({'cases': len(cases), 'valid': sum(o['valid'] for o in oracle), 'lean_accepts': sum(o['lean'] for o in oracle),
                      'lean_accepts_invalid': [o['name'] for o in oracle if o['lean'] and not o['valid']]}, indent=1))

if __name__ == '__main__':
    main()
