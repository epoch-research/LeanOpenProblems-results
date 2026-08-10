import FormalConjectures.Util.ProblemImports

open Lean Meta Elab Command

#eval show CommandElabM Unit from do
  let env ← getEnv
  let target ← liftTermElabM <| Term.elabType (← `(∀ P : Prop, P))
  let mut count := 0
  for (n, ci) in env.constants.toList do
    if ← liftTermElabM <| isDefEq ci.type target then
      logInfo m!"{n} : {ci.type}"
      count := count + 1
  logInfo m!"count {count}"
