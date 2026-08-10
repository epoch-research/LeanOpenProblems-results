import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command

def safe (axs : Array Name) := axs.all fun a => a == ``propext || a == ``Classical.choice || a == ``Quot.sound
elab "#inh_name_scan" : command => do
  let env ← getEnv
  let mut shown := 0
  for (name, ci) in env.constants.toList do
    if !(toString name).contains "Inhabited" then continue
    let fmt ← liftTermElabM <| ppExpr ci.type
    let s := fmt.pretty
    if s.contains "Prop" then
      try
        let axs ← liftTermElabM <| collectAxioms name
        if safe axs then
          logInfo m!"{name} : {ci.type} axs={axs}"
          shown := shown + 1
          if shown > 300 then break
      catch _ => pure ()
  logInfo m!"shown {shown}"
#inh_name_scan
