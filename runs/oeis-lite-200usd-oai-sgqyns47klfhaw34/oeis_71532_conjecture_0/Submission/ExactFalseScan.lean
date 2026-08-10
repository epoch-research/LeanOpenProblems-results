import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command
elab "#exact_false_scan" : command => do
  let env ← getEnv
  let mut shown := 0
  for (name, ci) in env.constants.toList do
    if ci.type.consumeMData == mkConst ``False then
      try
        let axs ← collectAxioms name
        let safe := axs.all (fun a => a == ``propext || a == ``Classical.choice || a == ``Quot.sound)
        if safe then
          logInfo m!"{name} : {ci.type} axs={axs}"
          shown := shown + 1
      catch _ => pure ()
  logInfo m!"shown {shown}"
#exact_false_scan
