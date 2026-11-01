"""Open Nat equations `∀ x y : Nat, lhs = rhs := rfl` between offset/literal forms.

Each pair is a random term over `x y : Nat` mixing literals (around the u64
boundary too), `+`, `Nat.succ`, `Nat.add`, `*`, `-`, `/`, `%`, `Nat.pred`,
and a rewrite of it that may or may not preserve definitional equality.
Lean's kernel decides definitional equality (`E{i}`, or `E{i}_f` added
unchecked when it refuses); Python evaluates both sides on a grid to know
whether the equation is even true. A checker accepting a false one is unsound.
"""

from __future__ import annotations

import argparse
import json
import os
import random
import subprocess
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

BIG = [2**64 - 1, 2**64, 2**32, 2**63]


def lit() -> int:
    r = random.random()
    if r < 0.6:
        return random.randint(0, 4)
    if r < 0.8:
        return random.choice(BIG)
    return random.choice(BIG) + random.randint(-2, 2)


# terms: ("x",) ("y",) ("lit", n) (op, a, b) / ("succ", a) ("pred", a)
def rnd(d: int):
    if d <= 0 or random.random() < 0.25:
        r = random.random()
        return ("x",) if r < 0.4 else ("y",) if r < 0.6 else ("lit", lit())
    k = random.choice(["add", "add", "add", "nadd", "succ", "succ", "mul", "sub", "pred", "div", "mod"])
    if k in ("succ", "pred"):
        return (k, rnd(d - 1))
    if k in ("mul", "div", "mod", "sub") and random.random() < 0.7:
        return (k, rnd(d - 1), ("lit", lit()))
    return (k, rnd(d - 1), rnd(d - 1))


def ev(t, x, y):
    k = t[0]
    if k == "x": return x
    if k == "y": return y
    if k == "lit": return t[1]
    if k == "succ": return ev(t[1], x, y) + 1
    if k == "pred": return max(ev(t[1], x, y) - 1, 0)
    a, b = ev(t[1], x, y), ev(t[2], x, y)
    if k in ("add", "nadd"): return a + b
    if k == "mul": return a * b
    if k == "sub": return max(a - b, 0)
    if k == "div": return a // b if b else 0
    if k == "mod": return a % b if b else a
    raise ValueError(k)


def lean(t) -> str:
    k = t[0]
    if k in ("x", "y"): return k
    if k == "lit": return str(t[1])
    if k == "succ": return f"(Nat.succ {lean(t[1])})"
    if k == "pred": return f"(Nat.pred {lean(t[1])})"
    if k == "nadd": return f"(Nat.add {lean(t[1])} {lean(t[2])})"
    op = {"add": "+", "mul": "*", "sub": "-", "div": "/", "mod": "%"}[k]
    return f"({lean(t[1])} {op} {lean(t[2])})"


def rewrite(t):
    """One local rewrite somewhere in t; some are definitional, some only propositional, some false."""
    k = t[0]
    if len(t) > 1 and k != "lit" and random.random() < 0.5:
        i = random.randrange(1, len(t))
        return t[:i] + (rewrite(t[i]),) + t[i + 1:]
    r = random.randrange(14)
    if r == 0 and k in ("add", "nadd") and t[2][0] == "lit" and t[2][1] > 0:
        return ("succ", (k, t[1], ("lit", t[2][1] - 1)))          # t + (n+1) ~> succ (t + n)
    if r == 1 and k == "succ":
        return ("add", t[1], ("lit", 1))                           # succ t ~> t + 1
    if r == 2 and k in ("add", "nadd") and t[1][0] in ("add", "nadd") and t[2][0] == "lit" and t[1][2][0] == "lit":
        return ("add", t[1][1], ("lit", t[1][2][1] + t[2][1]))     # (t + a) + b ~> t + (a+b)
    if r == 3 and k in ("add", "nadd"):
        return (k, t[2], t[1])                                     # commute (not definitional)
    if r == 4:
        return ("add", t, ("lit", 0))                              # t ~> t + 0
    if r == 5:
        return ("add", ("lit", 0), t)                              # t ~> 0 + t (not definitional)
    if r == 6 and k == "lit":
        return ("lit", t[1] + random.choice([-1, 1]))              # off by one (false)
    if r == 7 and k == "lit" and t[1] > 0:
        return ("succ", ("lit", t[1] - 1))                         # n+1 ~> succ n
    if r == 8:
        return ("pred", ("succ", t))                               # t ~> pred (succ t)
    if r == 9:
        return ("sub", ("add", t, ("lit", (n := lit()))), ("lit", n))  # t ~> (t + n) - n
    if r == 10 and k in ("add", "nadd"):
        return ("add" if k == "nadd" else "nadd", t[1], t[2])      # notation swap
    if r == 11:
        return ("mul", t, ("lit", 1))                              # t * 1
    if r == 12 and k == "succ":
        return ("succ", ("succ", t[1]))                            # extra succ (false)
    if r == 13 and k == "lit":
        return ("add", ("lit", (a := random.randint(0, t[1]))), ("lit", t[1] - a))
    return ("add", t, ("lit", 1)) if random.random() < 0.3 else t


GRID = [0, 1, 2, 3, 5, 2**32, 2**64 - 1, 2**64, 2**64 + 7, 12345678901234567890123]


def equiv(a, b) -> bool:
    return all(ev(a, x, y) == ev(b, x, y) for x in GRID for y in GRID[::3])


LEAN_PRELUDE = '''import Lean
open Lean Meta Elab
set_option maxRecDepth 100000
set_option maxHeartbeats 20000
set_option Elab.async false

def tryEq (n : Name) (l r : Name) : MetaM Bool := do
  let some (.defnInfo lv) := (← getEnv).find? l | throwError "no {l}"
  let some (.defnInfo rv) := (← getEnv).find? r | throwError "no {r}"
  let nat := mkConst ``Nat
  let lb := lv.value.bindingBody!.bindingBody!
  let rb := rv.value.bindingBody!.bindingBody!
  let ty := mkForall `x .default nat (mkForall `y .default nat (mkApp3 (mkConst ``Eq [1]) nat lb rb))
  let pf := mkLambda `x .default nat (mkLambda `y .default nat (mkApp2 (mkConst ``Eq.refl [1]) nat lb))
  let d := Declaration.thmDecl { name := n, levelParams := [], type := ty, value := pf }
  let before := (← getThe Core.State).messages.toList.length
  let ok ← try addDecl d; pure true catch _ => pure false
  let ok := ok && (← getThe Core.State).messages.toList.length == before && (← getEnv).contains n
  modifyThe Core.State fun s => { s with messages := {} }
  unless ok do
    withOptions (debug.skipKernelTC.set · true) <|
      addDecl (.thmDecl { name := n.appendAfter "_f", levelParams := [], type := ty, value := pf })
  return ok
'''


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("output", type=Path)
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--pairs", type=int, default=300)
    ap.add_argument("--depth", type=int, default=3)
    ap.add_argument("--workers", type=int, default=6)
    ap.add_argument("--lean", default=str(Path.home() / ".elan/toolchains/leanprover--lean4---v4.35.0/bin/lean"))
    a = ap.parse_args()
    random.seed(a.seed)
    pairs = []
    while len(pairs) < a.pairs:
        x = rnd(random.randint(1, a.depth))
        y = x
        for _ in range(random.randint(1, 3)):
            y = rewrite(y)
        if x != y:
            pairs.append((x, y, equiv(x, y)))
    a.output.mkdir(parents=True, exist_ok=False)
    lines = [LEAN_PRELUDE]
    for i, (x, y, _) in enumerate(pairs):
        lines += [f"def L{i} (x y : Nat) : Nat := {lean(x)}", f"def R{i} (x y : Nat) : Nat := {lean(y)}",
                  "run_meta do", f"  let r ← tryEq `E{i} `L{i} `R{i}",
                  f'  IO.FS.withFile "lean.txt" .append fun h => h.putStrLn s!"E{i} {{r}}"']
    (a.output / "Nq.lean").write_text("\n".join(lines) + "\n")
    prefix = subprocess.check_output([a.lean, "--print-prefix"], text=True).strip()
    env = {**os.environ, "LEAN_PATH": f"{a.output}:{prefix}/lib/lean"}
    p = subprocess.run([a.lean, "-o", "Nq.olean", "Nq.lean"], cwd=a.output, env=env, capture_output=True, text=True)
    if p.returncode:
        print(p.stdout[-3000:], p.stderr[-2000:])
        raise SystemExit(1)
    verdicts = dict(l.split() for l in (a.output / "lean.txt").read_text().splitlines())
    (a.output / "ex").mkdir()

    def export(i: int) -> None:
        name = f"E{i}" if verdicts[f"E{i}"] == "true" else f"E{i}_f"
        out = subprocess.run([str(Path(prefix) / "bin/leanexport"), "Nq", "--", name],
                             cwd=a.output, env=env, capture_output=True, text=True, check=True).stdout
        (a.output / "ex" / f"{name}.ndjson").write_text(out)

    with ThreadPoolExecutor(a.workers) as pool:
        list(pool.map(export, range(len(pairs))))
    oracle = [{"name": f"E{i}", "lhs": lean(x), "rhs": lean(y), "true": eq, "lean": verdicts[f"E{i}"] == "true"}
              for i, (x, y, eq) in enumerate(pairs)]
    (a.output / "oracle.json").write_text(json.dumps(oracle, indent=1))
    print(json.dumps({"pairs": len(pairs), "true": sum(o["true"] for o in oracle),
                      "lean_accepts": sum(o["lean"] for o in oracle),
                      "lean_accepts_false": [o["name"] for o in oracle if o["lean"] and not o["true"]]}, indent=1))


if __name__ == "__main__":
    main()
