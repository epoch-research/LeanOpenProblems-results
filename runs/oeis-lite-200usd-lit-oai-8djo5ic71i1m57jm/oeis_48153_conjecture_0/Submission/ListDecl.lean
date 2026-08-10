import FormalConjectures.Util.ProblemImports

#eval show Lean.CoreM Unit from do
  let env ← Lean.getEnv
  for (n, ci) in env.constants.toList do
    let s := toString n
    if (s.contains "sq" || s.contains "Square" || s.contains "quadratic" || s.contains "Quadratic") && (s.contains "mod" || s.contains "Mod" || s.contains "residue" || s.contains "Residue" || s.contains "sum" || s.contains "Sum") then
      IO.println s
