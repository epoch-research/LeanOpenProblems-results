import FormalConjectures.Util.ProblemImports
open Lean
#eval show CoreM Unit from do
  let env ← getEnv
  for (n, ci) in env.constants.toList do
    let s := toString n
    if (s.contains "floor" || s.contains "Floor" || s.contains "div") && (s.contains "sum" || s.contains "Sum" || s.contains "range" || s.contains "Ico") then
      IO.println s
