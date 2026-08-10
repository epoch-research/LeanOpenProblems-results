import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command
#eval show CommandElabM Unit from do
  let env ← getEnv
  for (name, ci) in env.constants.toList do
    let ns := toString name
    if ns.contains "exists_prime" || ns.contains "prime_gt" || ns.contains "prime_lt" || ns.contains "prime_between" || ns.contains "exists.*Prime" then
      logInfo m!"{name} : {ci.type}"
