import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command
#eval show CommandElabM Unit from do
  let env ← getEnv
  for (name, ci) in env.constants.toList do
    let ns := toString name
    if ns.startsWith "Chebyshev." then
      let s := toString ci.type
      if s.contains "theta" || s.contains "psi" || s.contains "primeCounting" then
        logInfo m!"{name} : {ci.type}"
