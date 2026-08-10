import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command
elab "#target_type_search" : command => do
  let env ← getEnv
  let mut shown := 0
  for (n, ci) in env.constants.toList do
    let fmt ← liftTermElabM <| ppExpr ci.type
    let s := fmt.pretty
    if s.contains "floor" || s.contains "⌊" || s.contains "3 / 2" || (toString n).contains "71532" then
      logInfo m!"{n} : {fmt}"
      shown := shown + 1
      if shown > 500 then break
  logInfo m!"shown {shown}"
#target_type_search
