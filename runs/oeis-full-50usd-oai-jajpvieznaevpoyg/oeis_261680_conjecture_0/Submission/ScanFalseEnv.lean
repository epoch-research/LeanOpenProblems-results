import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command

#eval show CommandElabM Unit from do
  let env ← getEnv
  let falseExpr := mkConst ``False
  let mut count := 0
  for (n, ci) in env.constants.toList do
    let t := ci.type
    if t == falseExpr then
      logInfo m!"FALSE DECL {n}"
      count := count + 1
  logInfo m!"count {count}"
