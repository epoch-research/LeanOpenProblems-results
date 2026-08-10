import FormalConjectures.Util.ProblemImports

#eval show Lean.CoreM Unit from do
  let env ← Lean.getEnv
  for (n, ci) in env.constants.toList do
    let s := toString n
    if (s.contains "Dirichlet" || s.contains "LFunction" || s.contains "character" || s.contains "Char" || s.contains "legendre" || s.contains "jacobi") && (s.contains "pos" || s.contains "Pos" || s.contains "zero" || s.contains "Zero" || s.contains "sum" || s.contains "Sum" || s.contains "nonneg" || s.contains "Nonneg") then
      IO.println s
