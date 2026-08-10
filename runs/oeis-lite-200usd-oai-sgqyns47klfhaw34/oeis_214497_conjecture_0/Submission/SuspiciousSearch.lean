import FormalConjectures.Util.ProblemImports

open Lean Meta Elab Command

#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut count := 0
  let mut shown := 0
  for (name, ci) in env.constants.toList do
    let t := ci.type
    let s := toString t
    if s.contains "0 = 1" || s.contains "1 = 0" || s.contains "False" || s.contains "Empty" || s.contains "PEmpty" then
      count := count + 1
      if shown < 200 then
        logInfo m!"{name} : {t}"
        shown := shown + 1
  logInfo m!"count {count}, shown {shown}"
