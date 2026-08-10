import FormalConjectures.Util.ProblemImports
open Lean Elab Command
#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut shown := 0
  let mut count := 0
  for (name, ci) in env.constants.toList do
    let ns := toString name
    let ts := toString ci.type
    if (ns.contains "false" || ns.contains "False" || ts.endsWith "False" || ts.contains "→ False") && shown < 500 then
      count := count + 1
      logInfo m!"{name} : {ci.type}"
      shown := shown + 1
  logInfo m!"count>= {count}, shown {shown}"
