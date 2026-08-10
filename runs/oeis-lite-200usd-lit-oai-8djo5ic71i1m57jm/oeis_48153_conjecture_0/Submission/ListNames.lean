import FormalConjectures.Util.ProblemImports
open Lean Meta in
#eval show CoreM Unit from do
  let env ← getEnv
  let mut arr := #[]
  for (n, c) in env.constants.toList do
    let s := toString n
    let sl := s.toLower
    if ((sl.contains "quadratic" || sl.contains "residue" || sl.contains "legendre" || sl.contains "zmod" || sl.contains "mod") && (sl.contains "sum" || sl.contains "half" || sl.contains "excess" || sl.contains "positive" || sl.contains "nonneg" || sl.contains "le" || sl.contains "lt")) then
      arr := arr.push s
  arr := arr.qsort (· < ·)
  for s in arr do
    IO.println s
