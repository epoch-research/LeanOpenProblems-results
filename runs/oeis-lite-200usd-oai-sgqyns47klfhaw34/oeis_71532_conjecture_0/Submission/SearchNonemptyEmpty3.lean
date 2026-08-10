import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command

#eval show CommandElabM Unit from do
  let env ← getEnv
  let target := mkApp (mkConst ``Nonempty [levelOne]) (mkConst ``Empty)
  for (n, ci) in env.constants.toList do
    if n.isInternal then continue
    if ci.isUnsafe then continue
    liftTermElabM <| withoutModifyingState do
      let (xs, _, body) ← forallMetaTelescopeReducing ci.type
      if (← isDefEq body target) then
        let e := mkAppN (mkConst n (ci.levelParams.map Level.param)) xs
        let t ← instantiateMVars (← inferType e)
        logInfo m!"unifies {n} : {← ppExpr t} FROM {← ppExpr ci.type}"
  logInfo m!"done"
