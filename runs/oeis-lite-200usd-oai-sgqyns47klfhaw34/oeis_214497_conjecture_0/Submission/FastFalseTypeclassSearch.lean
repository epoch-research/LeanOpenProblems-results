import FormalConjectures.Util.ProblemImports

open Lean Meta Elab Command

def allowedAx : Name → Bool
| `propext => true
| `Classical.choice => true
| `Quot.sound => true
| _ => false

partial def finalIsFalse : Expr → Bool
| .forallE _ _ b _ => finalIsFalse b
| e => e.isConstOf ``False

partial def noExplicit : Expr → Bool
| .forallE _ _ b bi => bi != BinderInfo.default && noExplicit b
| _ => true

partial def mkImplicitApp (e ty : Expr) : MetaM Expr := do
  let ty ← whnf ty
  match ty with
  | .forallE _ d b bi =>
      if bi == BinderInfo.default then throwError "explicit"
      let m ← mkFreshExprMVar d
      if bi == BinderInfo.instImplicit then
        let inst ← synthInstance d
        m.mvarId!.assign inst
      mkImplicitApp (mkApp e m) (b.instantiate1 m)
  | _ =>
      unless (← isDefEq ty (mkConst ``False)) do throwError "not false"
      instantiateMVars e

elab "#fast_false_typeclass_search" : command => do
  liftTermElabM do
    let env ← getEnv
    let mut tried := 0
    let mut hits := 0
    for (name, ci) in env.constants.toList do
      if ci.isUnsafe then continue
      let s := toString ci.type
      if !(s.contains "False") then continue
      if !(finalIsFalse ci.type) then continue
      if !(noExplicit ci.type) then continue
      let ax ← collectAxioms name
      if ! ax.all allowedAx then continue
      tried := tried + 1
      let res ← try
        withoutModifyingState do
          let levels ← ci.levelParams.mapM (fun _ => mkFreshLevelMVar)
          let e ← mkImplicitApp (mkConst name levels) (ci.type.instantiateLevelParams ci.levelParams levels)
          if e.hasExprMVar then pure none else pure (some e)
      catch _ => pure none
      if let some e := res then
        hits := hits + 1
        logInfo m!"HIT {name}: {ci.type} TERM {e} AX {ax.toList}"
    logInfo m!"tried={tried} hits={hits}"

#fast_false_typeclass_search
