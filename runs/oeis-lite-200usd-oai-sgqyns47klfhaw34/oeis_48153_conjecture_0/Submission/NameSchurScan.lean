import FormalConjectures.Util.ProblemImports
open Lean
#eval show CoreM Unit from do
  let env ← getEnv
  for (n, ci) in env.constants.toList do
    let s := toString n
    if s.contains "Schur" || s.contains "Brauer" || (s.contains "residue" && s.contains "sq") || (s.contains "mod" && s.contains "bound" && s.contains "sq") then
      IO.println s
