import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command

def safe (axs : Array Name) := axs.all fun a => a == ``propext || a == ``Classical.choice || a == ``Quot.sound

elab "#inhabited_prop_param_scan" : command => do
  let env ← getEnv
  let mut shown := 0
  for (name, ci) in env.constants.toList do
    if name.isInternal then continue
    let t := ci.type.consumeMData
    let fmt ← liftTermElabM <| ppExpr t
    let s := fmt.pretty
    if s.contains "Inhabited" && s.contains "Prop" then
      try
        let axs ← liftTermElabM <| collectAxioms name
        if safe axs then
          logInfo m!"{name} : {t} axs={axs}"
          shown := shown + 1
          if shown > 500 then break
      catch _ => pure ()
  logInfo m!"shown {shown}"
#inhabited_prop_param_scan
