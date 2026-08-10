import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command

#eval show CoreM Unit from do
  let env ← getEnv
  let mut arr := #[]
  for (n, ci) in env.constants.toList do
    let s := toString n
    if (s.contains "prime" || s.contains "Prime" || s.contains "Bertrand" || s.contains "Chebyshev") then
      arr := arr.push s
  arr := arr.qsort (· < ·)
  for s in arr do
    if (s.contains "exists" || s.contains "forall" || s.contains "tendsto" || s.contains "eventually" || s.contains "Counting" || s.contains "gap" || s.contains "modEq") then
      IO.println s
