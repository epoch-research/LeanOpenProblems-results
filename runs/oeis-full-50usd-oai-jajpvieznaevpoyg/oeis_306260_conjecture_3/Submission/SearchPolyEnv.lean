import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command
#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut found := #[]
  for (n,ci) in env.constants.toList do
    let s := toString n
    let t := toString ci.type
    if s.contains "triangle" || s.contains "Triangle" || s.contains "polygon" || s.contains "Polygon" || s.contains "pentagonal" || s.contains "Pentagonal" || s.contains "gauss" || s.contains "Gauss" || s.contains "eureka" || s.contains "Eureka" || t.contains "triangular" || t.contains "polygon" || t.contains "pentagonal" then
      found := found.push (s ++ " : " ++ t)
  found := found.qsort (· < ·)
  for x in found do logInfo x
