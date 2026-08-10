import FormalConjectures.Util.ProblemImports
open Lean Elab Command
#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut arr := #[]
  for (n, ci) in env.constants.toList do
    let s := n.toString
    if (s.contains "LFunction" || s.contains "LSeries" || s.contains "zetaMul") &&
       (s.contains "pos" || s.contains "positive" || s.contains "nonneg" || s.contains "zero" || s.contains "one") then
      arr := arr.push s
  arr := arr.qsort (· < ·)
  for s in arr do logInfo s
