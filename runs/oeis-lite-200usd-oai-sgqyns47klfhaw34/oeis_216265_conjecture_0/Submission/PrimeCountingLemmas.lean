import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command
#eval show CommandElabM Unit from do
  let env ← getEnv
  for (name, ci) in env.constants.toList do
    let ns := toString name
    if ns.contains "primeCounting" || ns.contains "primesBelow" || ns.contains "count_strict" || ns.contains "exists_of_count" then
      logInfo m!"{name} : {ci.type}"
