import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command
#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut count := 0
  for (name, ci) in env.constants.toList do
    let ns := toString name
    if ns.startsWith "FormalConjectures" || ns.startsWith "ProblemAttributes" || ns.startsWith "Google" then
      count := count + 1
      if count ≤ 300 then logInfo m!"{name} : {ci.type}"
  logInfo m!"total {count}"
