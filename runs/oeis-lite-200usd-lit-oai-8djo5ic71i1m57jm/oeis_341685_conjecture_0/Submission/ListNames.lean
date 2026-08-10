import FormalConjectures.Util.ProblemImports
open Lean Elab Command
#eval show CommandElabM Unit from do
  let env ← getEnv
  for (n, ci) in env.constants.toList do
    let s := toString n
    if s.contains "diam" || s.contains "LogDensity" || s.contains "VCDimAtMost" || s.contains "annihilation" then
      logInfo m!"{n}"
