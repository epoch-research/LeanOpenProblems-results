import FormalConjectures.Util.ProblemImports
open Lean Elab Command
#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut shown := 0
  let mut count := 0
  for (name, ci) in env.constants.toList do
    let s := toString ci.type
    if (s.contains "Nat.Prime" || s.contains ".Prime") && s.contains "- 1" && s.contains "+ 1" then
      count := count + 1
      if shown < 300 then
        logInfo m!"{name} : {ci.type}"
        shown := shown + 1
  logInfo m!"count={count}, shown={shown}"
