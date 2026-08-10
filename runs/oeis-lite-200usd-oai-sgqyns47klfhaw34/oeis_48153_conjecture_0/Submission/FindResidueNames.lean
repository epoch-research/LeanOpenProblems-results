import FormalConjectures.Util.ProblemImports
open Lean Elab Command
#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut arr := #[]
  for (n, ci) in env.constants.toList do
    let s := n.toString
    if (s.contains "residue" || s.contains "Residue" || s.contains "least" || s.contains "Least" || s.contains "quadratic" || s.contains "Quadratic" || s.contains "Legendre" || s.contains "legendre" || s.contains "jacobi" || s.contains "Jacobi") then
      arr := arr.push s
  arr := arr.qsort (· < ·)
  for s in arr do logInfo s
