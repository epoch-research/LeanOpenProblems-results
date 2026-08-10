import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command
partial def concl : Expr → Expr | .forallE _ _ b _ => concl b | e => e
elab "#sorry_power" : command => do
  let env ← getEnv
  let mut shown := 0
  for (name, ci) in env.constants.toList do
    if name.isInternal then continue
    try
      let axs ← collectAxioms name
      if axs.contains `sorryAx then
        let c := concl ci.type.consumeMData
        if c == mkConst ``False || (toString ci.type).contains "∀ (P : Prop), P" then
          logInfo m!"{name} : {ci.type} axs={axs}"
          shown := shown + 1
          if shown > 100 then break
    catch _ => pure ()
  logInfo m!"shown {shown}"
#sorry_power
