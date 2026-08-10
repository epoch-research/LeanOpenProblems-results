import FormalConjectures.Util.ProblemImports
open Lean
#eval show CoreM Unit from do
  let env ← getEnv
  for (n, ci) in env.constants.toList do
    let s := toString n
    if s.contains "LFunction_apply_one_ne_zero_of_quadratic" then
      IO.println s
