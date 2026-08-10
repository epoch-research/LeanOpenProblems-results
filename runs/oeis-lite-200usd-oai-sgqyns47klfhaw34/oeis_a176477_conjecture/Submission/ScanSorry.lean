import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command
#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut count := 0
  for (n, ci) in env.constants.toList do
    if count < 50 then
      if ci.type.isConstOf ``False then
        logInfo m!"False decl {n}"
        count := count + 1
