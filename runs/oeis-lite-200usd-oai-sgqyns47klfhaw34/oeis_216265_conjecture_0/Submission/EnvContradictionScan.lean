import FormalConjectures.Util.ProblemImports

open Lean Meta Elab Command

#eval show CommandElabM Unit from do
  let env ← getEnv
  for (name, ci) in env.constants.toList do
    let s := toString ci.type
    if s == "False" || s.contains "Empty" || s.contains "PUnit → False" || s.contains "¬True" then
      logInfo m!"{name} : {ci.type}"
