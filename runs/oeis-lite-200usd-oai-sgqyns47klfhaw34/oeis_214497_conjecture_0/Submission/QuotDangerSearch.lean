import FormalConjectures.Util.ProblemImports

open Lean Meta Elab Command

elab "#quot_danger_search" : command => do
  liftTermElabM do
    let env ← getEnv
    let mut shown := 0
    for (name, ci) in env.constants.toList do
      let ns := toString name
      let s := toString ci.type
      if (ns.contains "Quot" || s.contains "Quot") &&
         (s.contains "=" || s.contains "Relation" || s.contains "out" || s.contains "sound" || s.contains "exact" || s.contains "Nonempty" || s.contains "False") then
        if shown < 600 then
          logInfo m!"{name} : {ci.type}"
          shown := shown + 1
    logInfo m!"shown={shown}"

#quot_danger_search
