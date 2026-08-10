import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command

#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut n := 0
  for (name, ci) in env.constants.toList do
    let s := toString ci.type
    if (s.contains "IsAlgebraic" || s.contains "Algebra.IsAlgebraic" || s.contains "Transcendental") &&
       (s.contains "Padic" || s.contains "ℚ_[" || s.contains "padic" || s.contains "tsum" || s.contains "Summable") then
      logInfo m!"{name} : {ci.type}"
      n := n + 1
      if n > 300 then
        logInfo m!"stopping"
        return
  logInfo m!"count {n}"
