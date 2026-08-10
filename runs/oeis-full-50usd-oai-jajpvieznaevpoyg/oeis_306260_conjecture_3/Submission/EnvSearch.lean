import FormalConjectures.Util.ProblemImports
open Lean Elab Command
#eval show CoreM Unit from do
  let env ← getEnv
  let mut arr := #[]
  for (n, ci) in env.constants.toList do
    let s := toString n
    if (s.contains "Universal" || s.contains "universal" || s.contains "Represent" || s.contains "represent" || s.contains "Regular" || s.contains "regular" || s.contains "QuadraticForm") then
      if (s.contains "Nat" || s.contains "Int" || s.contains "Quadratic" || s.contains "Form" || s.contains "NumberTheory" || s.contains "Is") then
        arr := arr.push s
  IO.println s!"count {arr.size}"
  for s in (arr.qsort (· < ·)).take 1000 do IO.println s
