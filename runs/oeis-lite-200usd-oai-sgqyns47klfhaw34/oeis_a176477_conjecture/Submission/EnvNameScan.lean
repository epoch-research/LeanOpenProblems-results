import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command
#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut cnt := 0
  for (n, ci) in env.constants.toList do
    let s := n.toString
    if ((s.contains "choose" || s.contains "centralBinom" || s.contains "catalan") &&
        (s.contains "dvd" || s.contains "factor" || s.contains "div" || s.contains "modEq")) then
      logInfo m!"{n} : {ci.type}"
      cnt := cnt+1
      if cnt > 300 then break
  logInfo m!"count {cnt}"
