import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command
#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut c := 0
  for (n, ci) in env.constants.toList do
    let s := toString ci.type
    if s.contains "ModEq" then
      logInfo m!"{n} : {ci.type}"
      c := c + 1
      if c >= 300 then break
  logInfo m!"count {c}"
