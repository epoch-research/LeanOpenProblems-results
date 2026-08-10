import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command
#eval show CommandElabM Unit from do
  let env ← getEnv
  let falseExpr := mkConst ``False
  let mut c := 0
  for (name, info) in env.constants.toList do
    let b ← liftCoreM <| Meta.MetaM.toIO (isDefEq info.type falseExpr) {} { env := env }
    if b then
      logInfo m!"FALSE: {name}"
      c := c+1
  logInfo m!"false count {c}"
