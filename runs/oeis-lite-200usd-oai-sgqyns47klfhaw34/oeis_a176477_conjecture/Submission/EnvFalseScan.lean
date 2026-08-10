import FormalConjectures.Util.ProblemImports
open Lean Elab Command
#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut count := 0
  for (n, ci) in env.constants.toList do
    if ci.type.isConstOf ``False then
      IO.println s!"FALSE const: {n} : {ci.type}"
      count := count + 1
      if count > 50 then break
  IO.println s!"count {count}"
