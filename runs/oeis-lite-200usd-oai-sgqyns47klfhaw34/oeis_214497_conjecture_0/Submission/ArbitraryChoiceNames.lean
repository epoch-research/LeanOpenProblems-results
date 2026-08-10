import FormalConjectures.Util.ProblemImports

open Lean Meta Elab Command

elab "#arbitrary_choice_names" : command => do
  liftTermElabM do
    let env ← getEnv
    let mut shown := 0
    for (name, ci) in env.constants.toList do
      let ns := toString name
      let s := toString ci.type
      if (ns.contains "arbitrary" || ns.contains "choice" || ns.contains "complete" || ns.contains "decidable" || ns.contains "Nonempty" || ns.contains "Inhabited") &&
         (s.contains "Nonempty" || s.contains "Inhabited" || s.contains "Decidable" || s.contains "Prop" || s.contains "Sort") then
        if shown < 700 then
          logInfo m!"{name} : {ci.type}"
          shown := shown + 1
    logInfo m!"shown={shown}"

#arbitrary_choice_names
