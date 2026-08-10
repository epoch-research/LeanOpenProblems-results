import FormalConjectures.Util.ProblemImports
set_option maxHeartbeats 8000000
open Lean Meta Elab Command

partial def mkCandidate (ty : Expr) : MetaM (Option Expr) := do
  let ty ← whnf ty
  -- try typeclass synthesis first
  try
    let e ← synthInstance ty
    return some e
  catch _ => pure ()
  -- try Inhabited.default
  try
    let e ← mkAppM ``default #[ty]
    return some e
  catch _ => pure ()
  -- direct known closed inhabitants for small/common types
  if (← isDefEq ty (mkConst ``Nat)) then return some (mkNatLit 0)
  if (← isDefEq ty (mkConst ``Int)) then return some (toExpr (0 : Int))
  if (← isDefEq ty (mkConst ``Bool)) then return some (mkConst ``Bool.false)
  if (← isDefEq ty (mkSort levelZero)) then return some (mkConst ``True)
  return none

elab "#scan_neg_inst_decide" : command => do
  liftTermElabM do
    let env ← getEnv
    let printedRef ← IO.mkRef (0 : Nat)
    for (n, ci) in env.constants.toList do
      if (← printedRef.get) > 50 then return ()
      let ty := ci.type
      forallTelescope ty fun xs body => do
        if xs.size == 0 || xs.size > 5 then return ()
        unless body.isAppOfArity ``Not 1 do return ()
        let mut args : Array Expr := #[]
        let mut ok := true
        for x in xs do
          let d ← x.fvarId!.getDecl
          -- only try implicit/inst/default binders to avoid arbitrary theorem hypotheses
          if d.binderInfo == BinderInfo.default then ok := false
          if ok then
            match (← mkCandidate d.type) with
            | some e => args := args.push e
            | none => ok := false
        unless ok do return ()
        let app := mkAppN (mkConst n (ci.levelParams.map Level.param)) args
        let appTy ← inferType app >>= instantiateMVars
        forallTelescope appTy fun ys body2 => do
          if ys.size != 0 then return ()
          unless body2.isAppOfArity ``Not 1 do return ()
          let p := body2.appArg!
          try
            let _ ← synthInstance (← mkAppM ``Decidable #[p])
            let d ← mkAppM ``decide #[p]
            let dv ← whnf d
            if dv.isConstOf ``true then
              printedRef.modify (· + 1)
              logInfo m!"CANDIDATE {n}\n  app={app}\n  P={p}"
          catch _ => pure ()

#scan_neg_inst_decide
