import FormalConjectures.Util.ProblemImports

open Lean Meta Elab Command

#eval show CommandElabM Unit from do
  let env ← getEnv
  let targets := #[
    (← liftTermElabM <| Term.elabType (← `(∀ {P : Prop}, P))),
    (← liftTermElabM <| Term.elabType (← `(∀ P : Prop, P))),
    (← liftTermElabM <| Term.elabType (← `(False)))
  ]
  let mut count := 0
  for (name, ci) in env.constants.toList do
    if count < 100 then
      for tgt in targets do
        let ok ← liftTermElabM <| isDefEq ci.type tgt
        if ok then
          let axs ← collectAxioms name
          logInfo m!"MATCH {name} : {ci.type}; axioms={axs.toList}"
          count := count + 1
