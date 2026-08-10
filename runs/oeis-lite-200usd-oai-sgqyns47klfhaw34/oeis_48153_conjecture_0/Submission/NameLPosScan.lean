import FormalConjectures.Util.ProblemImports
open Lean
#eval show CoreM Unit from do
  let env ← getEnv
  for (n, ci) in env.constants.toList do
    let s := toString n
    if (s.contains "LFunction" || s.contains "LSeries" || s.contains "DirichletCharacter" || s.contains "quadratic" || s.contains "Quadratic") &&
       (s.contains "positive" || s.contains "Positive" || s.contains "pos" || s.contains "Pos" || s.contains "zero_lt" || s.contains "lt_zero" || s.contains "nonneg" || s.contains "Nonneg") then
      IO.println s
