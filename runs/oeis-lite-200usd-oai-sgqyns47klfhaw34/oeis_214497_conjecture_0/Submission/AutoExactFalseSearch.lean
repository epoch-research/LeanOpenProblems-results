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

partial def hasExplicitBinder : Expr → Bool
| .forallE _ _ b bi => bi == BinderInfo.default || hasExplicitBinder b
| _ => false

partial def mkFalseApp (fn : Expr) (ty : Expr) : MetaM Expr := do
  let ty ← whnf ty
  match ty with
  | .forallE _ d b bi =>
      if bi == BinderInfo.default then
        throwError "explicit binder"
      let m ← mkFreshExprMVar d
      let fn' := mkApp fn m
      let ty' := b.instantiate1 m
      if bi == BinderInfo.instImplicit then
        try
          let inst ← synthInstance d
          m.mvarId!.assign inst
        catch _ => pure ()
      mkFalseApp fn' ty'
  | _ =>
      unless (← isDefEq ty (mkConst ``False)) do
        throwError "result not false: {ty}"
      instantiateMVars fn

elab "#auto_exact_false_search" : command => do
  liftTermElabM do
    let env ← getEnv
    let mut shown := 0
    let mut tried := 0
    for (name, ci) in env.constants.toList do
      if ci.isUnsafe then continue
      if ! finalIsFalse ci.type then continue
      if hasExplicitBinder ci.type then continue
      let ax ← collectAxioms name
      if ! ax.all allowedAx then continue
      tried := tried + 1
      let hit? ← try
        withoutModifyingState do
          let levels ← ci.levelParams.mapM (fun _ => mkFreshLevelMVar)
          let e ← mkFalseApp (mkConst name levels) (ci.type.instantiateLevelParams ci.levelParams levels)
          let t ← inferType e
          if e.hasExprMVar then
            pure none
          else if ← isDefEq t (mkConst ``False) then
            pure (some e)
          else pure none
        catch _ => pure none
      if let some e := hit? then
        logInfo m!"HIT {name} : {ci.type} AX {ax.toList} TERM {e}"
        shown := shown + 1
    logInfo m!"tried={tried} hits={shown}"

#auto_exact_false_search
