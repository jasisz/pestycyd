import Gen
open Lean Meta

namespace PestycydGen

/-- A random inductive block, built directly as kernel terms. -/
structure Block where
  lparams : List Name
  nparams : Nat
  indexed : Bool
  /-- With `indexed`: the index is a `Nat` rather than a `Bool`. -/
  natIndex : Bool := false
  types : List InductiveType

/-- Richer sorts over two universe parameters, for `--rich`. -/
def richSort : M Level := do
  let u := mkLevelParam `u
  let v := mkLevelParam `v
  match ← rand 10 with
  | 0 => return u
  | 1 => return v
  | 2 => return mkLevelMax u v
  | 3 => return mkLevelSucc (mkLevelMax u v)
  | 4 => return mkLevelMax Level.one (mkLevelIMax u v)
  | 5 => return mkLevelIMax v (mkLevelSucc u)
  | 6 => return mkLevelMax (mkLevelSucc u) v
  | 7 => return mkLevelIMax u v
  | 8 => return mkLevelSucc v
  | _ => return Level.zero

def sortFor (poly : Bool) : M Level := do
  let u := mkLevelParam `u
  if poly then
    match ← rand 6 with
    | 0 => return u
    | 1 => return mkLevelMax Level.one u
    | 2 => return mkLevelSucc u
    | 3 => return mkLevelIMax Level.one u
    | 4 => return mkLevelMax u Level.one
    | _ => return Level.zero
  else
    match ← rand 4 with
    | 0 => return Level.zero
    | 1 => return Level.zero
    | 2 => return Level.one
    | _ => return mkLevelSucc Level.one

/-- Hide `e : Sort l` behind a redex the kernel must reduce to see it:
a vacuous beta, a vacuous `let`, or `@id (Sort l) e`. -/
def hide (rate : Nat) (l : Level) (e : Expr) : M Expr := do
  if rate == 0 then return e
  unless ← chance rate do return e
  match ← rand 3 with
  | 0 => return mkApp (.lam `h (mkConst ``Bool) e .default) (mkConst ``Bool.true)
  | 1 => return .letE `h (mkConst ``Bool) (mkConst ``Bool.true) e false
  | _ => return mkApp2 (mkConst ``id [mkLevelSucc l]) (mkSort l) e

/-- A field of type `e` that mentions `occ : Sort l` (a member of the block)
only in a part the kernel's weak head normalisation discards: the argument of
a constant function, or the value of an unused `let`, sometimes under a
negative arrow. Lean's positivity check reduces first and accepts it. -/
def vanish (rate : Nat) (l : Level) (occ e : Expr) : M Expr := do
  if rate == 0 then return e
  unless ← chance (rate / 2) do return e
  let (arg, sort) := if ← chance 50 then (occ, mkSort l)
    else (.forallE `y occ e .default, mkSort (mkLevelIMax l Level.one))
  if ← chance 50 then
    return mkApp (.lam `X sort e .default) arg
  else
    return .letE `X sort arg e false

def genBlock (base : Name) (hideRate : Nat := 0) (rich : Bool := false) : M Block := do
  let poly ← chance (if rich then 70 else 40)
  let twoLevels := rich && poly && (← chance 60)
  let lparams := if twoLevels then [`u, `v] else if poly then [`u] else []
  let us := lparams.map mkLevelParam
  let lvl ← if twoLevels then richSort else sortFor poly
  let ntypes := if ← chance 25 then 2 else 1
  let names := (List.range ntypes).map fun j => base ++ Name.mkSimple s!"T{j}"
  let nparams ← rand 3
  let indexed ← chance (if rich then 60 else 45)
  let natIndex := rich && indexed && (← chance 60)
  let idxTy := mkConst (if natIndex then ``Nat else ``Bool)
  let paramLevel := if twoLevels && (← chance 50) then mkLevelParam `v
    else if poly then mkLevelParam `u else Level.one
  let rec withParams (left : Nat) (params : Array Expr) : M Block := do
    if left > 0 then
      withLocalDeclD (Name.mkSimple s!"α{left}") (mkSort paramLevel) fun p =>
        withParams (left - 1) (params.push p)
    else
      let mut types : List InductiveType := []
      for i in [0:ntypes] do
        let name := names[i]!
        let result := mkSort lvl
        let type ← mkForallFVars params <|
          if indexed then .forallE `idx idxTy result .default else result
        let mut ctors : List Constructor := []
        let nctors := 1 + (← rand 4)
        for j in [0:nctors] do
          let cname := name ++ Name.mkSimple s!"c{j}"
          let idx : Expr ← if natIndex then pure (mkRawNatLit (← rand 3))
            else pure (mkConst (if ← chance 50 then ``Bool.true else ``Bool.false))
          let target (which : Nat) : Expr :=
            mkAppN (mkConst names[which]! us)
              (if indexed then params.push idx else params)
          let result := target i
          let mut fields : Array Expr := #[]
          let mut ctorBody := result
          if j > 0 then
            let shape ← rand 11
            if indexed && (shape == 9 || shape == 10) then
              let atIndex (index : Expr) := mkAppN (mkConst name us) (params.push index)
              ctorBody := if natIndex then
                let succ (e : Expr) := mkApp (mkConst ``Nat.succ) e
                if shape == 9 then
                  .forallE `n idxTy (atIndex (succ (.bvar 0))) .default
                else
                  .forallE `n idxTy
                    (.forallE `x (atIndex (.bvar 0)) (atIndex (succ (.bvar 1))) .default) .default
              else if shape == 9 then
                .forallE `b (mkConst ``Bool) (atIndex (.bvar 0)) .default
              else
                .forallE `b (mkConst ``Bool)
                  (.forallE `x (atIndex (.bvar 0)) (atIndex (.bvar 1)) .default) .default
            else if shape == 0 then
              fields := fields.push (← vanish hideRate lvl (target i)
                (← hide hideRate Level.one (mkConst ``Bool)))
            else if shape == 1 then
              fields := fields.push (← vanish hideRate lvl (target i)
                (← hide hideRate Level.one (mkConst ``Nat)))
            else if shape == 2 && params.size > 0 then
              fields := fields.push (← hide hideRate paramLevel params[← rand params.size]!)
            else
              let which := if ntypes > 1 && (← chance 40) then (i + 1) % ntypes else i
              let child ← hide hideRate lvl (target which)
              let field := if let .succ elementLevel := lvl then
                if shape == 3 then mkApp (mkConst ``List [elementLevel]) child
                else if shape == 5 then mkApp (mkConst ``Option [elementLevel]) child
                else if shape == 6 then
                  mkApp2 (mkConst ``Prod [elementLevel, Level.zero]) child (mkConst ``Nat)
                else if shape == 7 then mkApp (mkConst ``Array [elementLevel]) child
                else if shape == 8 then
                  mkApp (mkConst ``Option [elementLevel])
                    (mkApp (mkConst ``List [elementLevel]) child)
                else if shape == 4 then .forallE `b (mkConst ``Bool) child .default
                else child
              else if shape == 4 then .forallE `b (mkConst ``Bool) child .default
              else child
              fields := fields.push (← hide hideRate lvl field)
          if ctorBody == result then
            if j > 1 && (← chance 40) then
              fields := fields.push (mkConst ``Bool)
            ctorBody := fields.foldr (fun field body => Expr.forallE `x field body .default) result
          let ctorType ← mkForallFVars params ctorBody
          ctors := ctors ++ [{ name := cname, type := ctorType }]
        types := types ++ [({ name, type, ctors } : InductiveType)]
      return { lparams, nparams, indexed, natIndex, types }
  withParams nparams #[]

def runInd (seed count : Nat) (hideRate : Nat := 0) (rich : Bool := false) : MetaM (Array Name × Array Expr × Nat) := do
  let mut good := #[]
  let mut targets := #[]
  let mut rejected := 0
  let mut st : GenState := { seed := seed * 2654435761 + 1 }
  for i in [0:count] do
    let base := Name.mkStr `PestycydInd s!"s{seed}x{i}"
    let (block, st') ← (genBlock base hideRate rich).run st
    st := st'
    let decl := Declaration.inductDecl block.lparams block.nparams block.types false
    if ← tryAdd decl then
      let names := decl.getNames.toArray
      good := good ++ names
      st := { st with extra := st.extra ++ names }
      for ty in block.types do
        let ps := (List.range block.nparams).toArray.map fun _ => mkConst ``Nat
        let us := block.lparams.map fun _ => Level.one
        let head := mkConst ty.name us
        if block.indexed && block.natIndex then
          for k in [0:4] do
            targets := targets.push (mkAppN head (ps.push (mkRawNatLit k)))
        else if block.indexed then
          targets := targets.push (mkAppN head (ps.push (mkConst ``Bool.true)))
          targets := targets.push (mkAppN head (ps.push (mkConst ``Bool.false)))
        else
          targets := targets.push (mkAppN head ps)
    else
      rejected := rejected + 1
  return (good, targets, rejected)

/-- Make an actual iota reduction do work: every motive returns Nat and every
minor returns zero, so a closed major must reduce to zero. -/
def recursorTheorem (recName : Name) (target : Expr) : M (Option (Expr × Expr)) := do
  let .recInfo recVal ← getConstInfo recName | return none
  let useResults ← chance 50
  let levels := recVal.levelParams.map fun _ => Level.one
  let (mvs, _, _) ← forallMetaTelescopeReducing
    (← instantiateTypeLevelParams recVal.toConstantVal levels)
  let args := target.getAppArgs
  if args.size != recVal.numParams + recVal.numIndices then return none
  for j in [0:recVal.numParams] do
    unless ← isDefEq mvs[j]! args[j]! do return none
  for j in [recVal.numParams:recVal.getFirstMinorIdx] do
    let ty ← instantiateMVars (← mvs[j]!.mvarId!.getType)
    let motive ← forallTelescopeReducing ty fun fvars _ =>
      mkLambdaFVars fvars (mkConst ``Nat)
    unless ← isDefEq mvs[j]! motive do return none
  for j in [recVal.getFirstMinorIdx:recVal.getFirstIndexIdx] do
    let ty ← instantiateMVars (← mvs[j]!.mvarId!.getType)
    let minor ← forallTelescopeReducing ty fun fvars _ => do
      let mut body := mkRawNatLit (if useResults then 1 else 0)
      if useResults then
        for fv in fvars do
          if ← isDefEq (← inferType fv) (mkConst ``Nat) then
            body := mkApp2 (mkConst ``Nat.add) body fv
      mkLambdaFVars fvars body
    unless ← isDefEq mvs[j]! minor do return none
  for j in [0:recVal.numIndices] do
    unless ← isDefEq mvs[recVal.getFirstIndexIdx + j]!
      args[recVal.numParams + j]! do return none
  let some major ← gen target 3 | return none
  unless ← isDefEq mvs[recVal.getMajorIdx]! major do return none
  let term ← instantiateMVars (mkAppN (mkConst recName levels) mvs)
  if term.hasMVar then return none
  unless ← isDefEq (← inferType term) (mkConst ``Nat) do return none
  let result ← withTransparency .all <| Meta.reduce term (skipTypes := false)
  unless (match result with | .lit (.natVal _) => true | _ => false) do return none
  unless ← isDefEq term result do return none
  return some (← mkEq term result, ← mkEqRefl term)

def runRec (seed count : Nat) (extra : Array Name) (targets : Array Expr) : MetaM (Array Name) := do
  let recursors := extra.filter fun n => n.getString! == "rec"
  let mut good := #[]
  let mut st : GenState := { seed := seed * 2654435761 + 1, extra }
  for i in [0:count] do
    if recursors.isEmpty then break
    let (result, st') ← (tryCatchRuntimeEx (do
      let recName := recursors[← rand recursors.size]!
      let choices := targets.filter fun (ty : Expr) => ty.getAppFn.constName! == recName.getPrefix
      if choices.isEmpty then return none
      recursorTheorem recName choices[← rand choices.size]!)
      (fun _ => pure none)).run st
    st := st'
    let some (ty, value) := result | continue
    let name := Name.mkStr `PestycydGen s!"r{seed}x{i}"
    let decl := Declaration.thmDecl { name, levelParams := [], type := ty, value }
    if ← tryAdd decl then good := good.push name
  return good
