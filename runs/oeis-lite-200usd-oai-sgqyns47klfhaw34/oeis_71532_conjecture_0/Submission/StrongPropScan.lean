import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command

def isSafeArr (axs : Array Name) : Bool := axs.all fun a => a == ``propext || a == ``Classical.choice || a == ``Quot.sound

elab "#strong_prop_scan" : command => do
  let env ← getEnv
  let mut shown := 0
  for (name, ci) in env.constants.toList do
    if name.isInternal then continue
    let t := ci.type.consumeMData
    match t with
    | .forallE _ (.sort .zero) body _ =>
      let fmt ← liftTermElabM <| ppExpr t
      let s := fmt.pretty
      if (s.contains "Nonempty" || s.contains "Inhabited" || s.contains "False" || s.contains "¬") then
        try
          let axs ← liftTermElabM <| collectAxioms name
          if isSafeArr axs then
            logInfo m!"{name} : {t} axs={axs}"
            shown := shown + 1
            if shown > 500 then break
        catch _ => pure ()
    | _ => pure ()
  logInfo m!"shown {shown}"
#strong_prop_scan
