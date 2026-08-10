import FormalConjectures.Util.ProblemImports

open Lean Meta Elab Command

partial def hasConst (nm : Name) (e : Expr) : Bool := e.getUsedConstants.contains nm

elab "#absurd_power_search" : command => do
  let env ← getEnv
  let mut printed := 0
  for (n, ci) in env.constants.toList do
    if printed >= 300 then break
    if n.isInternal then continue
    let ty := ci.type.consumeMData
    let mut cand := false
    match ty with
    | Expr.forallE _ dom body _ =>
      let dom ← liftTermElabM <| instantiateMVars dom
      if (← liftTermElabM <| isDefEq dom (mkSort levelZero)) then
        -- ∀ P : Prop, ... P ...
        cand := true
      let body' := body.consumeMData
      match body' with
      | Expr.bvar 0 => cand := true
      | Expr.app (Expr.const ``Nonempty _) (Expr.bvar 0) => cand := true
      | _ => pure ()
    | _ => pure ()
    if cand || (toString n).contains "lcProof" || (toString n).contains "proof" && hasConst ``False ty then
      let pp ← liftTermElabM <| Meta.ppExpr ci.type
      logInfo m!"{n} : {pp}"
      printed := printed + 1
  logInfo m!"printed {printed}"

#absurd_power_search
