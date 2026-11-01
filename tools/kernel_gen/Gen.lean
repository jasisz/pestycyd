import Lean
open Lean Meta

namespace PestycydGen

structure GenState where
  seed : Nat
  /-- Constants of inductives accepted earlier in the run, favoured by `gen`. -/
  extra : Array Name := #[]

abbrev M := StateRefT GenState MetaM

def rand (n : Nat) : M Nat := do
  let st ← get
  let s' := (st.seed * 6364136223846793005 + 1442695040888963407) % 18446744073709551616
  set { st with seed := s' }
  return (s' / 65536) % (max n 1)

def chance (k : Nat) : M Bool := return (← rand 100) < k

def pool : Array Name := #[
  ``Nat.zero, ``Nat.succ, ``Nat.add, ``Nat.mul, ``Nat.sub, ``Nat.div, ``Nat.mod, ``Nat.pred,
  ``Nat.beq, ``Nat.ble, ``Nat.rec, ``Nat.casesOn, ``Nat.pow, ``Nat.gcd, ``Nat.land,
  ``Bool.true, ``Bool.false, ``Bool.rec, ``cond, ``not, ``and, ``or,
  ``Prod.mk, ``Prod.fst, ``Prod.snd, ``Prod.rec,
  ``List.nil, ``List.cons, ``List.length, ``List.rec, ``List.map, ``List.foldl, ``List.append,
  ``Option.none, ``Option.some, ``Option.rec, ``Option.getD,
  ``id, ``Function.const, ``Function.comp, ``PUnit.unit, ``PUnit.rec,
  ``Sum.inl, ``Sum.inr, ``Sum.rec, ``Sigma.mk, ``Sigma.fst, ``Sigma.snd,
  ``PProd.mk, ``PProd.fst, ``ULift.up, ``ULift.down, ``Subtype.mk, ``Subtype.val,
  ``True.intro, ``And.intro, ``Eq.refl, ``Eq.rec, ``Eq.symm, ``congrArg, ``Quot.mk, ``Quot.lift]

/-- Small ground types to aim at. -/
def baseTypes : M Expr := do
  match ← rand 9 with
  | 0 | 1 | 2 => return mkConst ``Nat
  | 3 => return mkConst ``Bool
  | 4 => return mkApp2 (mkConst ``Prod [1, 1]) (mkConst ``Nat) (mkConst ``Bool)
  | 5 => return mkApp (mkConst ``List [0]) (mkConst ``Nat)
  | 6 => return mkApp (mkConst ``Option [0]) (mkConst ``Nat)
  | 7 => return mkForall `x .default (mkConst ``Nat) (mkConst ``Nat)
  | _ => return mkApp2 (mkConst ``Sum [0, 0]) (mkConst ``Bool) (mkConst ``Nat)

partial def gen (ty : Expr) (fuel : Nat) : M (Option Expr) := do
  let ty ← whnfR (← instantiateMVars ty)
  if let .forallE n d b bi := ty then
    return ← withLocalDecl n bi d fun x => do
      let some v ← gen (b.instantiate1 x) fuel | return none
      return some (← mkLambdaFVars #[x] v)
  -- locals first, sometimes
  let lctx ← getLCtx
  let mut cands : Array (M (Option Expr)) := #[]
  for d in lctx do
    unless d.isImplementationDetail do
      let fv := d.toExpr
      cands := cands.push do
        if ← isDefEq d.type ty then return some fv else return none
  if ty.isConstOf ``Nat then
    cands := cands.push do
      let k ← rand 6
      let a ← rand 5
      let b ← rand 20
      let n := if k == 0 then 18446744073709551616 + a
        else if k == 1 then 4294967296 - a else b
      return some (mkRawNatLit n)
  if let .sort u := ty then
    cands := cands.push do
      if u == Level.one then return some (← baseTypes) else return none
  if fuel > 0 then
    let extra := (← get).extra
    if let .const n _ := ty.getAppFn then
      for c in extra do
        if c.getPrefix == n && c != n && c.getString! != "rec" then
          cands := cands.push (tryConst c ty (fuel - 1))
    if ty.isConstOf ``Nat then
      let recursors := extra.filter (fun c => c.getString! == "rec")
      for _ in [0:2] do
        if recursors.size > 0 then
          cands := cands.push (tryConst recursors[← rand recursors.size]! ty (fuel - 1))
    for _ in [0:6] do
      let c ← if extra.size > 0 && (← chance 50) then pure extra[← rand extra.size]!
        else pure pool[← rand pool.size]!
      cands := cands.push (tryConst c ty (fuel - 1))
  -- shuffle by picking random candidates
  let mut tries := 0
  while tries < 8 && cands.size > 0 do
    tries := tries + 1
    let i ← rand cands.size
    let s : Meta.SavedState ← liftM (m := MetaM) saveState
    match ← (try cands[i]! catch _ => pure none) with
    | some e => return some e
    | none => liftM (m := MetaM) s.restore
  return none
where
  tryConst (c : Name) (ty : Expr) (fuel : Nat) : M (Option Expr) := do
    let info ← getConstInfo c
    let us ← info.levelParams.mapM fun _ => mkFreshLevelMVar
    let f := mkConst c us
    let (mvs, _, res) ← forallMetaTelescopeReducing (← instantiateTypeLevelParams info.toConstantVal us)
    unless ← isDefEq res ty do return none
    for mv in mvs do
      let mv := mv.mvarId!
      unless ← mv.isAssigned do
        let some v ← gen (← instantiateMVars (← mv.getType)) fuel | return none
        unless ← isDefEq (.mvar mv) v do return none
    let e ← instantiateMVars (mkAppN f mvs)
    if e.hasMVar then return none
    return some e

def ground (e : Expr) : MetaM Expr := do
  let e ← instantiateMVars e
  -- universe metavariables left over become `1`/`0` pseudo-randomly fixed at zero
  let e := e.replaceLevel fun
    | .mvar _ => some Level.zero
    | _ => none
  return e

def tryAdd (d : Declaration) : CoreM Bool := do
  let before := (← get).messages.toList.length
  try
    withOptions (fun o => Elab.async.set o false) (addDecl d)
  catch _ => return false
  -- a kernel error reported as a message rather than thrown still counts as a rejection
  return (← get).messages.toList.length == before && d.getNames.all (← getEnv).contains

def tryAddUnchecked (d : Declaration) : CoreM Unit := do
  withOptions (fun o => debug.skipKernelTC.set o true) (addDecl d)

/-- Perturb one random subterm: the near-miss. -/
partial def perturb (e : Expr) : M Expr := do
  let target ← rand 12
  let rec go (e : Expr) (k : Nat) : M (Expr × Nat) := do
    if k == target then
      match e with
      | .lit (.natVal n) => return (.lit (.natVal (n + 1)), k + 1)
      | .bvar i => return (.bvar (i + 1), k + 1)
      | .const n us => return (.const n (us.map fun u => mkLevelSucc u), k + 1)
      | .app f a => return (.app a f, k + 1)
      | .sort u => return (.sort (mkLevelSucc u), k + 1)
      | e => return (e, k + 1)
    match e with
    | .app f a => do let (f, k) ← go f (k + 1); let (a, k) ← go a k; return (.app f a, k)
    | .lam n t b bi => do let (t, k) ← go t (k + 1); let (b, k) ← go b k; return (.lam n t b bi, k)
    | .forallE n t b bi => do let (t, k) ← go t (k + 1); let (b, k) ← go b k; return (.forallE n t b bi, k)
    | e => return (e, k + 1)
  return (← go e 0).1

def run (seed count : Nat) (extra : Array Name := #[]) (targets : Array Expr := #[]) : MetaM (Array Name × Array Name) := do
  let mut good := #[]
  let mut bad := #[]
  let mut st : GenState := { seed := seed * 2654435761 + 1, extra }
  for i in [0:count] do
    let (r, st') ← (tryCatchRuntimeEx (do
      let ty ← if targets.size > 0 && (← chance 60) then
        pure targets[← rand targets.size]!
      else baseTypes
      let some v ← gen ty 4 | return none
      let v ← ground v
      let ty ← ground ty
      let asThm ← chance 50
      if asThm && (← inferType ty).isProp then return none
      if asThm then
        -- theorem `v = whnf v` checked by rfl
        let r ← withTransparency .all <| Meta.reduce v (skipTypes := false)
        let stmt ← mkEq v r
        let pf ← mkEqRefl v
        return some (stmt, pf, true)
      return some (ty, v, false)) (fun _ => pure none)).run st
    st := st'
    let some (ty, v, isThm) := r | continue
    let name := Name.mkStr `PestycydGen s!"g{seed}x{i}"
    let mk (ty v : Expr) : Declaration :=
      if isThm then .thmDecl { name, levelParams := [], type := ty, value := v }
      else .defnDecl { name, levelParams := [], type := ty, value := v, hints := .abbrev, safety := .safe }
    if ← tryAdd (mk ty v) then
      good := good.push name
      -- one near miss per accepted declaration
      let ((ty2, v2), st') ← (do
        if ← chance 50 then return (← perturb ty, v) else return (ty, ← perturb v)).run st
      st := st'
      let bname := Name.mkStr `PestycydGen s!"b{seed}x{i}"
      let rename (n : Name) : Declaration := match mk ty2 v2 with
        | .thmDecl t => Declaration.thmDecl { t with name := n, all := [n] }
        | .defnDecl t => Declaration.defnDecl { t with name := n, all := [n] }
        | d => d
      if ty2 == ty && v2 == v then continue
      -- a failed check still occupies its name, so the kernel sees a scratch copy
      if ← tryAdd (rename (bname.appendAfter "_chk")) then
        if ← tryAdd (rename bname) then good := good.push bname
      else
        try tryAddUnchecked (rename bname); bad := bad.push bname catch _ => pure ()
  return (good, bad)

end PestycydGen
