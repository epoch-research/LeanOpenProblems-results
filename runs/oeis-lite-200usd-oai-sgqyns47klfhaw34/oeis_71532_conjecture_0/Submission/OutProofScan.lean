import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command

def safe (axs : Array Name) := axs.all fun a => a == ``propext || a == ``Classical.choice || a == ``Quot.sound
elab "#outproof_scan" : command => do
  let env ← getEnv
  let mut shown := 0
  for (n, ci) in env.constants.toList do
    let ns := toString n
    if !(ns.contains "out" || ns.contains "proof" || ns.contains "sound" || ns.contains "eval" || ns.contains "Proof" || ns.contains "mk") then continue
    let t := ci.type.consumeMData
    match t with
    | .forallE _ (.sort .zero) _ _ =>
      try
        let axs ← liftTermElabM <| collectAxioms n
        if safe axs then
          let fmt ← liftTermElabM <| ppExpr t
          let s:=fmt.pretty
          if s.contains "→ p" || s.contains "→ a" || s.contains "→ P" || s.contains ": Prop" then
            logInfo m!"{n} : {fmt} axs={axs}"
            shown:=shown+1
            if shown>500 then break
      catch _ => pure ()
    | _ => pure ()
  logInfo m!"shown {shown}"
#outproof_scan
