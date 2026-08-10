import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command

#eval show CommandElabM Unit from do
  let env ← getEnv
  let target := mkApp (mkConst ``Nonempty [levelOne]) (mkConst ``Empty)
  for (n, ci) in env.constants.toList do
    if n.isInternal then continue
    if ci.isUnsafe then continue
    liftTermElabM <| do
      let us := ci.levelParams.map (fun _ => levelZero)
      let ty ← inferType (mkConst n us)
      let (xs, _, body) ← forallMetaTelescopeReducing ty
      if (← isDefEq body target) then
        let e := mkAppN (mkConst n us) xs
        let t ← instantiateMVars (← inferType e)
        logInfo m!"unifies {n} : {← ppExpr t}"
  logInfo m!"done"
