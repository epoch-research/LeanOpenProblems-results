import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command
#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut cnt := 0
  for (n, ci) in env.constants.toList do
    if n.getRoot == `Classical then
      let s := toString ci.type
      if s.contains "Nonempty" || s.contains "Decidable" || s.contains "Prop" || s.contains "False" then
        logInfo m!"{n} : {ci.type}"
        cnt := cnt+1
        if cnt > 200 then break
