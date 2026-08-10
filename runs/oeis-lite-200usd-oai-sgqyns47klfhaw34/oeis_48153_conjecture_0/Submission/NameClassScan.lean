import FormalConjectures.Util.ProblemImports
open Lean
#eval show CoreM Unit from do
  let env ← getEnv
  for (n, ci) in env.constants.toList do
    let s := toString n
    if s.contains "Dedekind" || s.contains "dedekind" || s.contains "cot" || s.contains "Cot" || s.contains "classNumber" || s.contains "ClassNumber" || s.contains "Bernoulli" || s.contains "bernoulli" || s.contains "excess" || s.contains "Excess" then
      IO.println s
