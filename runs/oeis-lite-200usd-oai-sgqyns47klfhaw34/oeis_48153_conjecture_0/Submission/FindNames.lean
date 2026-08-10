import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command
#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut arr := #[]
  for (n, ci) in env.constants.toList do
    let s := n.toString
    if (s.contains "mod" || s.contains "Mod" || s.contains "residue" || s.contains "Residue" || s.contains "floor" || s.contains "Floor" || s.contains "Legendre" || s.contains "legendre") &&
       (s.contains "sum" || s.contains "Sum" || s.contains "quadr" || s.contains "Quadr" || s.contains "sq" || s.contains "Sq" || s.contains "card" || s.contains "Card") then
      arr := arr.push s
  arr := arr.qsort (· < ·)
  for s in arr do logInfo s
