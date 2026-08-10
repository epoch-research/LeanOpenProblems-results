import FormalConjectures.Util.ProblemImports

#eval show Lean.CoreM Unit from do
  let env ← Lean.getEnv
  for (n, ci) in env.constants.toList do
    let s := toString n
    if (s.contains "residue" || s.contains "Residue" || s.contains "least" || s.contains "Least" || s.contains "valMin" || s.contains "quadraticChar" || s.contains "legendreSym") && (s.contains "sum" || s.contains "Sum" || s.contains "card" || s.contains "Card" || s.contains "pos" || s.contains "nonneg" || s.contains "le" || s.contains "eq") then
      IO.println s
