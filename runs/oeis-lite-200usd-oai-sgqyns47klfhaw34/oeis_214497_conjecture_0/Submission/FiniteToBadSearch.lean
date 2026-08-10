import FormalConjectures.Util.ProblemImports
open Lean Elab Command
#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut shown := 0
  let mut count := 0
  for (n, ci) in env.constants.toList do
    let s := toString ci.type
    if (s.contains "Finite" || s.contains "Fintype") && (s.contains "Subsingleton" || s.contains "Infinite" || s.contains "Unique" || s.contains "Nontrivial") then
      count := count + 1
      if shown < 400 then
        logInfo m!"{n} : {ci.type}"
        shown := shown + 1
  logInfo m!"count={count}, shown={shown}"
