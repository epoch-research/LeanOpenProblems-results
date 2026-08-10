import FormalConjectures.Util.ProblemImports

open Lean Meta Elab Command

#eval show CommandElabM Unit from do
  let env ← getEnv
  let target ← liftTermElabM <| Term.elabType (← `(∀ {α : Sort u}, α))
  let mut count := 0
  for (n, ci) in env.constants.toList do
    -- print exact syntactic-ish matches containing forall and unsafe, using rough string filter
    if toString ci.type |>.contains "∀ {α : Sort" then
      logInfo m!"{n} unsafe {ci.isUnsafe} : {ci.type}"
      count := count + 1
  logInfo m!"count {count}"
