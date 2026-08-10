import FormalConjectures.Util.ProblemImports
set_option maxHeartbeats 8000000
open Lean Meta Elab Command

partial def mkCandidate (ty : Expr) : MetaM (Option Expr) := do
  let ty ← whnf ty
  try return some (← synthInstance ty) catch _ => pure ()
  try return some (← mkAppM ``default #[ty]) catch _ => pure ()
  if (← isDefEq ty (mkConst ``Nat)) then return some (mkNatLit 0)
  if (← isDefEq ty (mkConst ``Int)) then return some (toExpr (0 : Int))
  if (← isDefEq ty (mkConst ``Bool)) then return some (mkConst ``Bool.false)
  if (← isDefEq ty (mkSort levelZero)) then return some (mkConst ``True)
  return none

elab "#scan_false_inst" : command => do
  liftTermElabM do
    let env ← getEnv
    let printedRef ← IO.mkRef (0 : Nat)
    for (n, ci) in env.constants.toList do
      if (← printedRef.get) > 100 then return ()
      let ty := ci.type
      forallTelescope ty fun xs body => do
        if xs.size == 0 || xs.size > 7 then return ()
        let bodyWhnf ← whnf body
        unless bodyWhnf.isConstOf ``False do return ()
        let mut args : Array Expr := #[]
        let mut ok := true
        for x in xs do
          let d ← x.fvarId!.getDecl
          if d.binderInfo == BinderInfo.default then ok := false
          if ok then
            match (← mkCandidate d.type) with
            | some e => args := args.push e
            | none => ok := false
        if ok then
          let app := mkAppN (mkConst n (ci.levelParams.map Level.param)) args
          try
            let appTy0 ← inferType app
            let appTy1 ← instantiateMVars appTy0
            let appTy ← whnf appTy1
            if appTy.isConstOf ``False then
              printedRef.modify (· + 1)
              logInfo m!"FALSE_CANDIDATE {n}\n  app={app}"
          catch _ => pure ()

#scan_false_inst
