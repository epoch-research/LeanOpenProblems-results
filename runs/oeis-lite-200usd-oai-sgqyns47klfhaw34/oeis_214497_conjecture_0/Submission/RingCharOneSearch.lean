import FormalConjectures.Util.ProblemImports
open Lean Elab Command
#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut shown := 0
  for (n, ci) in env.constants.toList do
    let s := toString ci.type
    if s.contains "CharP" && s.contains " 1" then
      if shown < 200 then logInfo m!"{n} : {ci.type}"
      shown := shown + 1
  logInfo m!"shown/count {shown}"
