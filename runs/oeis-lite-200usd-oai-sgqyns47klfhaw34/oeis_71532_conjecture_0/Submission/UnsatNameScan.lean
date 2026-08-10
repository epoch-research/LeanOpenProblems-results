import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command
elab "#unsat_names" : command => do
  let env ← getEnv
  let mut shown := 0
  for (n, ci) in env.constants.toList do
    if (toString n).contains "unsat" || (toString n).contains "Unsat" then
      let fmt ← liftTermElabM <| ppExpr ci.type
      logInfo m!"{n} : {fmt}"
      shown:=shown+1
      if shown>300 then break
  logInfo m!"shown {shown}"
#unsat_names
