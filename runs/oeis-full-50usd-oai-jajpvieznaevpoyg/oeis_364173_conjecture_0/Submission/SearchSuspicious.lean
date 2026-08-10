import FormalConjectures.Util.ProblemImports

open Lean Meta Elab Command

#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut count := 0
  for (n, ci) in env.constants.toList do
    let s := toString n
    if s.contains "false" || s.contains "False" || s.contains "contrad" || s.contains "inconsistent" then
      if count < 200 then logInfo m!"{n} : {ci.type}"
      count := count + 1
  logInfo m!"name count {count}"
