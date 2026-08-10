import FormalConjectures.Util.ProblemImports

open Lean Meta Elab Command

#eval show CommandElabM Unit from do
  let env ← getEnv
  let patterns := ["0 < 0", "1 < 0", "2 < 1", "0 = 1", "1 = 0", "0 ≠ 0", "1 ≠ 1", "2 ∣ 1", "3 ∣ 1"]
  let mut shown := 0
  let mut count := 0
  for (name, ci) in env.constants.toList do
    let s := toString ci.type
    if patterns.any (fun nd => s.contains nd) then
      count := count + 1
      if shown < 200 then
        logInfo m!"{name} : {ci.type}"
        shown := shown + 1
  logInfo m!"count={count}, shown={shown}"
