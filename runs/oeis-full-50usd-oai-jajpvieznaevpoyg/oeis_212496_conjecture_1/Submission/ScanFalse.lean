import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command
#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut count := 0
  for (n, ci) in env.constants.toList do
    let ty := ci.type
    if ty.isConstOf ``False then
      logInfo m!"False decl: {n}"
      count := count + 1
      if count > 50 then break
  logInfo m!"count shown {count}"
