import FormalConjectures.Util.ProblemImports
open Lean Elab Command
set_option maxHeartbeats 0
#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut printed := 0
  for (n, ci) in env.constants.toList do
    let s := n.toString
    if s.contains "Algebraic" || s.contains "algebraic" || s.contains "Transcend" || s.contains "transcend" then
      logInfo m!"{n}"
      printed := printed + 1
      if printed > 2000 then return
  logInfo m!"printed {printed}"
