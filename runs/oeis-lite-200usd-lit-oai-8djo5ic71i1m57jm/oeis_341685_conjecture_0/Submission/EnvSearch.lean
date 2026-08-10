import FormalConjectures.Util.ProblemImports

#eval show Lean.CoreM Unit from do
  let env ← Lean.getEnv
  for (n, ci) in env.constants.toList do
    if (toString n).contains "diam" || (toString n).contains "annihilationNumberEq" || (toString n).contains "hasLogDensity" then
      IO.println n
