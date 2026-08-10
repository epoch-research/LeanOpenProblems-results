import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command
#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut arr := #[]
  for (n,ci) in env.constants.toList do
    let s := toString n
    if s.contains "square" || s.contains "Square" || s.contains "sq" || s.contains "Sq" || s.contains "sum" || s.contains "Sum" || s.contains "nat" then
      if s.contains "three" || s.contains "Three" || s.contains "four" || s.contains "Four" || s.contains "legendre" || s.contains "Legendre" || s.contains "polygon" || s.contains "Polygon" || s.contains "triangular" || s.contains "Triangular" || s.contains "fermat" || s.contains "Fermat" then
        arr := arr.push s
  arr := arr.qsort (· < ·)
  for s in arr do logInfo s
