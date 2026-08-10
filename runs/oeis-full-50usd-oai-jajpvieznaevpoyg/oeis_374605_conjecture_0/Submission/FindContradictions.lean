import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command
#eval show CommandElabM Unit from do
  let env ← getEnv
  let t1 ← liftTermElabM <| Term.elabType (← `(((0 : Nat) = (1 : Nat))))
  let t2 ← liftTermElabM <| Term.elabType (← `(((1 : Nat) = (0 : Nat))))
  let t3 ← liftTermElabM <| Term.elabType (← `((Nonempty False)))
  let targets := #[t1,t2,t3]
  let allowed := [`propext, `Classical.choice, `Quot.sound]
  let mut count := 0
  for (name, ci) in env.constants.toList do
    for target in targets do
      if count < 50 then
        let ok ← liftTermElabM <| isDefEq ci.type target
        if ok then
          let axs ← collectAxioms name
          let bad := axs.toList.any (fun a => !allowed.contains a)
          if !bad then
            logInfo m!"ALLOWED CONTRA {name} : {ci.type}; axioms={axs.toList}"
            count := count + 1
  logInfo m!"done {count}"
