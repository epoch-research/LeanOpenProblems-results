import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command

#eval show CommandElabM Unit from do
  let env ← getEnv
  let target := mkApp (mkConst ``Nonempty [levelOne]) (mkConst ``Empty)
  for (n, ci) in env.constants.toList do
    if n.isInternal then continue
    if ci.isUnsafe then continue
    liftTermElabM <| forallTelescopeReducing ci.type fun xs body => do
      if !(body.hasLooseBVars) then
        if (← isDefEq body target) then
          logInfo m!"unifies {n} : {← ppExpr ci.type}"
  logInfo m!"done"
