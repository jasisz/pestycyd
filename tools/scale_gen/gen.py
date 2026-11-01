"""Scale ladders: self-contained valid NDJSON exports whose size grows along one axis.

Each shape is a small family of declarations built from `Sort` alone (no
prelude), parameterised by a depth n. Every export is valid, so any reject,
crash or timeout is a robustness or performance divergence. Run the main
checkers over a ladder of depths and compare how their time grows.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path

META = {"meta": {"exporter": {"name": "lean4export", "version": "3.1.0"},
                 "format": {"version": "3.1.0"},
                 "lean": {"githash": "pestycyd-generated", "version": "4.35.0"}}}


class Ex:
    def __init__(self) -> None:
        self.lines: list[dict] = [META]
        self.names: dict[tuple, int] = {}
        self.levels: dict[tuple, int] = {("zero",): 0}
        self.exprs: dict[str, int] = {}
        self.ne = 0

    def name(self, *parts: str) -> int:
        pre = 0
        for p in parts:
            key = (pre, p)
            if key not in self.names:
                idx = len(self.names) + 1
                self.names[key] = idx
                self.lines.append({"in": idx, "str": {"pre": pre, "str": p}})
            pre = self.names[key]
        return pre

    def lvl(self, kind: str, *args) -> int:
        key = (kind, *args)
        if key not in self.levels:
            idx = len(self.levels)
            self.levels[key] = idx
            body = {"succ": args[0]} if kind == "succ" else (
                {kind: list(args)} if kind in ("max", "imax") else {"param": args[0]})
            self.lines.append({"il": idx, **body})
        return self.levels[key]

    def e(self, kind: str, body) -> int:
        key = json.dumps([kind, body], sort_keys=True)
        if key not in self.exprs:
            self.exprs[key] = self.ne
            self.lines.append({"ie": self.ne, kind: body})
            self.ne += 1
        return self.exprs[key]

    def sort(self, l: int) -> int:
        return self.e("sort", l)

    def bvar(self, i: int) -> int:
        return self.e("bvar", i)

    def pi(self, ty: int, body: int, n: int = 0) -> int:
        return self.e("forallE", {"binderInfo": "default", "body": body, "name": n, "type": ty})

    def lam(self, ty: int, body: int, n: int = 0) -> int:
        return self.e("lam", {"binderInfo": "default", "body": body, "name": n, "type": ty})

    def app(self, f: int, a: int) -> int:
        return self.e("app", {"arg": a, "fn": f})

    def let(self, ty: int, val: int, body: int, n: int = 0) -> int:
        return self.e("letE", {"body": body, "name": n, "nondep": False, "type": ty, "value": val})

    def const(self, n: int, us: list[int] | None = None) -> int:
        return self.e("const", {"name": n, "us": us or []})

    def defn(self, n: int, ty: int, val: int, lps: list[int] | None = None, hints="abbrev") -> None:
        self.lines.append({"def": {"all": [n], "hints": hints, "levelParams": lps or [],
                                   "name": n, "safety": "safe", "type": ty, "value": val}})

    def thm(self, n: int, ty: int, val: int, lps: list[int] | None = None) -> None:
        self.lines.append({"thm": {"all": [n], "levelParams": lps or [], "name": n,
                                   "type": ty, "value": val}})

    def text(self) -> str:
        return "".join(json.dumps(x, separators=(",", ":")) + "\n" for x in self.lines)


def prop_true(x: Ex) -> tuple[int, int]:
    """`∀ p : Prop, p → p` and its proof `fun p h => h`."""
    prop = x.sort(0)
    ty = x.pi(prop, x.pi(x.bvar(0), x.bvar(1)))
    pf = x.lam(prop, x.lam(x.bvar(0), x.bvar(0)))
    return ty, pf


# Each shape: n -> Ex
def level_succ(n: int) -> Ex:
    """def T : Sort (n+2) := Sort (n+1)"""
    x = Ex()
    l = 0
    for _ in range(n + 1):
        l = x.lvl("succ", l)
    x.defn(x.name("T"), x.sort(x.lvl("succ", l)), x.sort(l))
    return x


def level_max_nest(n: int) -> Ex:
    """def T.{u} : Sort (max u (max u (… (max u 1)))+1) := Sort (max …): nested max of a param."""
    x = Ex()
    u = x.name("u")
    pu = x.lvl("param", u)
    l = x.lvl("succ", 0)
    for _ in range(n):
        l = x.lvl("max", pu, l)
    x.defn(x.name("T"), x.sort(x.lvl("succ", l)), x.sort(l), [u])
    return x


def level_imax_nest(n: int) -> Ex:
    """Same with imax u (imax u (… 1)), which normalises to max u 1."""
    x = Ex()
    u = x.name("u")
    pu = x.lvl("param", u)
    l = x.lvl("succ", 0)
    for _ in range(n):
        l = x.lvl("imax", pu, l)
    x.defn(x.name("T"), x.sort(x.lvl("succ", l)), x.sort(l), [u])
    return x


def level_eq_reassoc(n: int) -> Ex:
    """Defeq check between max(u1, max(u2, …)) and max(max(…, u_{n-1}), u_n): n level params."""
    x = Ex()
    ps = [x.name(f"u{i}") for i in range(n)]
    pl = [x.lvl("param", p) for p in ps]
    right = pl[-1]
    for p in reversed(pl[:-1]):
        right = x.lvl("max", p, right)
    left = pl[0]
    for p in pl[1:]:
        left = x.lvl("max", left, p)
    # def T : Sort (succ left) := Sort right
    x.defn(x.name("T"), x.sort(x.lvl("succ", left)), x.sort(right), ps)
    return x


def many_level_params(n: int) -> Ex:
    """def T.{u0 … un} : Type := Prop, then def U := T.{0,…,0} (instantiation with n levels)."""
    x = Ex()
    ps = [x.name(f"u{i}") for i in range(n)]
    for p in ps:  # nanoda-family parsers need a param record per declared parameter
        x.lvl("param", p)
    one = x.lvl("succ", 0)
    t = x.name("T")
    x.defn(t, x.sort(one), x.sort(0), ps)
    x.defn(x.name("U"), x.sort(one), x.const(t, [0] * n))
    return x


def long_name(n: int) -> Ex:
    """A declaration whose name has n components, referenced from another."""
    x = Ex()
    parts = [f"a{i % 7}" for i in range(n)]
    ln = x.name(*parts)
    ty, pf = prop_true(x)
    x.thm(ln, ty, pf)
    x.thm(x.name("B"), ty, x.const(ln))
    return x


def arrow_chain(n: int) -> Ex:
    """def T : Type := Prop → Prop → … → Prop (n arrows)."""
    x = Ex()
    prop = x.sort(0)
    t = prop
    for _ in range(n):
        t = x.pi(prop, t)
    x.defn(x.name("T"), x.sort(x.lvl("succ", 0)), t)
    return x


def dep_pi_chain(n: int) -> Ex:
    """theorem : ∀ p1 … pn : Prop, pn → pn, with the proof under n lambdas."""
    x = Ex()
    prop = x.sort(0)
    ty = x.pi(x.bvar(0), x.bvar(1))
    pf = x.lam(x.bvar(0), x.bvar(0))
    for _ in range(n):
        ty = x.pi(prop, ty)
        pf = x.lam(prop, pf)
    x.thm(x.name("T"), ty, pf)
    return x


def first_binder(n: int) -> Ex:
    """∀ p1 … pn : Prop, p1 → p1: body refers to the outermost binder (bvar n)."""
    x = Ex()
    prop = x.sort(0)
    ty = x.pi(x.bvar(n - 1), x.bvar(n))
    pf = x.lam(x.bvar(n - 1), x.bvar(0))
    for _ in range(n):
        ty = x.pi(prop, ty)
        pf = x.lam(prop, pf)
    x.thm(x.name("T"), ty, pf)
    return x


def let_chain(n: int) -> Ex:
    """let x1 : Prop := P; let x2 : Prop := x1; …; proof of x_n as P → P."""
    x = Ex()
    prop = x.sort(0)
    ty, pf = prop_true(x)
    p = x.name("P")
    x.defn(p, prop, ty)
    # value: let x1 := P; … let xn := x_{n-1}; (pf : xn)
    body = pf
    for _ in range(n):
        body = x.let(prop, x.bvar(0), body)
    body = x.let(prop, x.const(p), body) if n else body
    # innermost bvar(0) in the first let refers to … keep simple: each x_{k+1} := x_k
    x.thm(x.name("T"), x.const(p), body)
    return x


def let_ref_chain(n: int) -> Ex:
    """Type is the last let variable: forces zeta through the whole chain."""
    x = Ex()
    prop = x.sort(0)
    ty, pf = prop_true(x)
    p = x.name("P")
    x.defn(p, prop, ty)
    # fun (h : P) => let x1 : Prop := P; …; let xn : Prop := x_{n-1}; (h : xn)
    inner = x.bvar(n)  # h, under n lets
    # build inside-out: annotate with identity at type xn: (fun (y : xn) => y) h
    inner = x.app(x.lam(x.bvar(0), x.bvar(0)), inner)
    body = inner
    for k in range(n - 1, 0, -1):
        body = x.let(prop, x.bvar(0), body)
    body = x.let(prop, x.const(p), body)
    val = x.lam(x.const(p), body)
    x.thm(x.name("T"), x.pi(x.const(p), x.const(p)), val)
    return x


def beta_chain(n: int) -> Ex:
    """(fun y => y) ((fun y => y) (… pf)) at type P."""
    x = Ex()
    prop = x.sort(0)
    ty, pf = prop_true(x)
    p = x.name("P")
    x.defn(p, prop, ty)
    idf = x.lam(x.const(p), x.bvar(0))
    v = pf
    for _ in range(n):
        v = x.app(idf, v)
    x.thm(x.name("T"), x.const(p), v)
    return x


def delta_chain(n: int) -> Ex:
    """D0 := P, D(k+1) := Dk, theorem : Dn := pf (n unfoldings)."""
    x = Ex()
    prop = x.sort(0)
    ty, pf = prop_true(x)
    prev = x.name("D0")
    x.defn(prev, prop, ty, hints={"regular": 1})
    for k in range(1, n + 1):
        cur = x.name(f"D{k}")
        x.defn(cur, prop, x.const(prev), hints={"regular": k + 1})
        prev = cur
    x.thm(x.name("T"), x.const(prev), pf)
    return x


def delta_chain_both(n: int) -> Ex:
    """A(k) and B(k) two independent n-long chains to P; theorem: An → Bn via id."""
    x = Ex()
    prop = x.sort(0)
    ty, _ = prop_true(x)
    p = x.name("P")
    x.defn(p, prop, ty, hints={"regular": 1})
    ends = []
    for tag in "AB":
        prev = p
        for k in range(1, n + 1):
            cur = x.name(f"{tag}{k}")
            x.defn(cur, prop, x.const(prev), hints={"regular": k + 1})
            prev = cur
        ends.append(prev)
    x.thm(x.name("T"), x.pi(x.const(ends[0]), x.const(ends[1])), x.lam(x.const(ends[0]), x.bvar(0)))
    return x


def wide_decls(n: int) -> Ex:
    """n independent theorems."""
    x = Ex()
    ty, pf = prop_true(x)
    for k in range(n):
        x.thm(x.name(f"t{k}"), ty, pf)
    return x


def app_wide(n: int) -> Ex:
    """f : Prop → … → Prop (n args) applied to n arguments, as a type."""
    x = Ex()
    prop = x.sort(0)
    ty, _ = prop_true(x)
    t = prop
    for _ in range(n):
        t = x.pi(prop, t)
    f = x.name("F")
    # F := fun p1 … pn => pn
    v = x.bvar(0)
    for _ in range(n):
        v = x.lam(prop, v)
    x.defn(f, t, v)
    a = x.const(f)
    pname = x.name("P")
    x.defn(pname, prop, ty)
    for _ in range(n):
        a = x.app(a, x.const(pname))
    x.defn(x.name("G"), prop, a)
    return x


SHAPES = {f.__name__: f for f in [
    level_succ, level_max_nest, level_imax_nest, level_eq_reassoc, many_level_params,
    long_name, arrow_chain, dep_pi_chain, first_binder, let_chain, let_ref_chain,
    beta_chain, delta_chain, delta_chain_both, wide_decls, app_wide]}


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("output", type=Path)
    ap.add_argument("--depths", default="1000,10000,100000")
    ap.add_argument("--shape", action="append", choices=sorted(SHAPES))
    a = ap.parse_args()
    a.output.mkdir(parents=True, exist_ok=True)
    for name in a.shape or SHAPES:
        for n in map(int, a.depths.split(",")):
            (a.output / f"{name}-{n}.ndjson").write_text(SHAPES[name](n).text())
            print(name, n)


if __name__ == "__main__":
    main()
