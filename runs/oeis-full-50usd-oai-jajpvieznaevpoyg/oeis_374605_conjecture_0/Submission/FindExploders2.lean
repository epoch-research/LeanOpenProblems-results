import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command Term
#eval show CommandElabM Unit from do
  let env ← getEnv
  let allowed := [`propext, `Classical.choice, `Quot.sound]
  let stxs ← pure #[← `(∀ P : Prop, P), ← `(∀ {P : Prop}, P), ← `(∀ P : Prop, Nonempty P), ← `(∀ {P : Prop}, Nonempty P)]
  let mut count := 0
  for stx in stxs do
    let target ← liftTermElabM <| elabType stx
    for (name, ci) in env.constants.toList do
      if count < 50 then
        let ok ← liftTermElabM <| isDefEq ci.type target
        if ok then
          let axs ← collectAxioms name
          if !(axs.toList.any (fun a => !allowed.contains a)) then
            logInfo m!"ALLOWED {name} : {ci.type}; axioms={axs.toList}"
            count := count + 1
  logInfo m!"done {count}"
