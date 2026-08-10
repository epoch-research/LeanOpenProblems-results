import FormalConjectures.Util.ProblemImports
open Lean Meta
#eval show CoreM Unit from do
  for (n, ci) in (← getEnv).constants.toList do
    if toString ci.type |>.contains "shiftedLegendre" then
      IO.println s!"{n} : {ci.type}"
