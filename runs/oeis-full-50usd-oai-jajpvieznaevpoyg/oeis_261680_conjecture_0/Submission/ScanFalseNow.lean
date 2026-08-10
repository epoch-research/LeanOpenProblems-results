import FormalConjectures.Util.ProblemImports
open Lean Elab Command
#eval show CoreM Unit from do
  let env ← getEnv
  let mut c := 0
  for (n, ci) in env.constants.toList do
    if ci.type == mkConst ``False then
      IO.println s!"{n}"
      c := c+1
  IO.println s!"count {c}"
