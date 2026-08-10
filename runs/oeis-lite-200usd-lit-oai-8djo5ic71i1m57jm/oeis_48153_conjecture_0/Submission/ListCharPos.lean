import FormalConjectures.Util.ProblemImports
open Lean Meta in
#eval show CoreM Unit from do
  let env ← getEnv
  let mut out := #[]
  for (n,c) in env.constants.toList do
    let s := toString n; let sl := s.toLower
    if (sl.contains "dirichlet" || sl.contains "lfunction" || sl.contains "legendre" || sl.contains "mulchar" || sl.contains "quadraticchar" || sl.contains "gausssum" || sl.contains "zeta") &&
       (sl.contains "pos" || sl.contains "nonneg" || sl.contains "positive" || sl.contains "lt" || sl.contains "le" || sl.contains "sum") then
      out := out.push s
  out := out.qsort (· < ·)
  for s in out do IO.println s
