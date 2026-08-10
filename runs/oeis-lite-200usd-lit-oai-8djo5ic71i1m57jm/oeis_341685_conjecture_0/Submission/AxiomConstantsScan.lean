import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command
set_option maxHeartbeats 0
#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut n := 0
  for (name, ci) in env.constants.toList do
    match ci with
    | .axiomInfo ai =>
      if !(name.toString.contains "sorryAx") then
        let pp ← liftTermElabM <| ppExpr ai.type
        logInfo m!"AX {name} : {pp}"
        n := n + 1
        if n > 500 then return
    | _ => pure ()
  logInfo m!"count {n}"
