import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command
#eval show CommandElabM Unit from do
  let env ← getEnv
  let target ← liftTermElabM <| Term.elabType (← `(False))
  let allowed := [`propext, `Classical.choice, `Quot.sound]
  let mut count := 0
  for (name, ci) in env.constants.toList do
    if count < 50 then
      let ok ← liftTermElabM <| isDefEq ci.type target
      if ok then
        let axs ← collectAxioms name
        let bad := axs.toList.any (fun a => !allowed.contains a)
        if !bad then
          logInfo m!"ALLOWED FALSE {name}; axioms={axs.toList}"
          count := count + 1
  logInfo m!"done {count}"
