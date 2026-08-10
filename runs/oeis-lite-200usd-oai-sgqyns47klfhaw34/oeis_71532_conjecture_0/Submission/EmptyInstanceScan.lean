import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command

def safe (axs : Array Name) := axs.all fun a => a == ``propext || a == ``Classical.choice || a == ``Quot.sound
elab "#empty_inst_scan" : command => do
  let env ← getEnv
  let mut shown := 0
  for (name, ci) in env.constants.toList do
    let ns := toString name
    if !(ns.contains "IsEmpty" || ns.contains "Subsingleton" || ns.contains "Unique" || ns.contains "Nontrivial") then continue
    let fmt ← liftTermElabM <| ppExpr ci.type
    let s := fmt.pretty
    if (s.contains "IsEmpty" || s.contains "Subsingleton" || s.contains "Unique" || s.contains "Nontrivial") then
      try
        let axs ← liftTermElabM <| collectAxioms name
        if safe axs then
          logInfo m!"{name} : {ci.type} axs={axs}"
          shown := shown+1
          if shown > 800 then break
      catch _ => pure ()
  logInfo m!"shown {shown}"
#empty_inst_scan
