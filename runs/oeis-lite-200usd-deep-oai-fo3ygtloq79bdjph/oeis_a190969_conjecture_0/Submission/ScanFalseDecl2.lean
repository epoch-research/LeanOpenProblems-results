import FormalConjectures.Util.ProblemImports

open Lean Elab Command Meta

#eval show CommandElabM Unit from do
  let env ← getEnv
  let falseExpr := mkConst ``False
  let mut found := 0
  for (n, ci) in env.constants.toList do
    try
      let eq ← liftTermElabM <| isDefEq ci.type falseExpr
      if eq then
        logInfo m!"false theorem: {n}"
        found := found + 1
    catch _ => pure ()
  logInfo m!"found {found}"
