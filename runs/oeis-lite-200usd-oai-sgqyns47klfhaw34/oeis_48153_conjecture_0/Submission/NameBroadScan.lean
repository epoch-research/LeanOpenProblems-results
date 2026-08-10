import FormalConjectures.Util.ProblemImports
open Lean
#eval show CoreM Unit from do
  let env ← getEnv
  let mut out := #[]
  for (n, ci) in env.constants.toList do
    let s := toString n
    if ((s.contains "mod" || s.contains "Mod" || s.contains "floor" || s.contains "Floor" || s.contains "sqrt" || s.contains "Sqrt" || s.contains "sum" || s.contains "Sum") &&
        (s.contains "sq" || s.contains "Sq" || s.contains "square" || s.contains "Square" || s.contains "quadratic" || s.contains "Quadratic")) then
      out := out.push s
  for s in out.qsort (· < ·) do IO.println s
