import FormalConjectures.Util.ProblemImports
#eval show Lean.CoreM Unit from do
  let env ← Lean.getEnv
  for (n, ci) in env.constants.toList do
    let s := toString n
    if (s.contains "mod" || s.contains "Mod" || s.contains "emod" || s.contains "div") && (s.contains "sum" || s.contains "Sum" || s.contains "le" || s.contains "bound") then
      IO.println s
