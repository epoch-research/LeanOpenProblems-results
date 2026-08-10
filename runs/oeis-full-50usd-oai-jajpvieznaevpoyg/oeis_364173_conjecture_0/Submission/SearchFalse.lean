import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command
#eval show CoreM Unit from do
  let env ← getEnv
  let mut cnt := 0
  for (n, ci) in env.constants.toList do
    if ci.type.isConstOf ``False then
      IO.println s!"False decl {n}"
      cnt := cnt + 1
  IO.println s!"count {cnt}"
