import FormalConjectures.Util.ProblemImports
open Lean Elab Command
#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut c := 0
  for (n, ci) in env.constants.toList do
    if ci.type.isConstOf ``False then
      logInfo m!"{n} : {ci.type}"
      c := c+1
      if c > 50 then break
  logInfo m!"count shown {c}"
