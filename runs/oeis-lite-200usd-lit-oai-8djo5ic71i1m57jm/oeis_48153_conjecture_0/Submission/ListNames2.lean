import FormalConjectures.Util.ProblemImports
open Lean Meta in
#eval show CoreM Unit from do
  let env ← getEnv
  let keys := ["legendre", "quadraticchar", "quadratic", "dirichletcharacter.lfunction"]
  for (n, c) in env.constants.toList do
    let s := toString n; let sl := s.toLower
    if keys.any (fun k => sl.contains k) && !(sl.contains "module") then
      if (sl.contains "sum" || sl.contains "positive" || sl.contains "nonneg" || sl.contains "half" || sl.contains "excess" || sl.contains "one" || sl.contains "zero" || sl.contains "neg") then
        IO.println s
