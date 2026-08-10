import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command

elab "#formal_closed_search" : command => do
  let env ← getEnv
  let mut printed := 0
  for (n, ci) in env.constants.toList do
    if printed >= 300 then break
    let ns := toString n
    if !(ns.startsWith "FormalConjectures" || ns.startsWith "gold" || ns.contains "Conjecture" || ns.contains "Fermat" || ns.contains "oeis") then continue
    if (← liftTermElabM <| isProp ci.type) then
      let pp ← liftTermElabM <| Meta.ppExpr ci.type
      logInfo m!"{n} : {pp}"
      printed := printed + 1
  logInfo m!"printed {printed}"
#formal_closed_search
