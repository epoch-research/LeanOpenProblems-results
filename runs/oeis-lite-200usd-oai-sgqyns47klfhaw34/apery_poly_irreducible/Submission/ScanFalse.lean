import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command
#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut count := 0
  for (n, ci) in env.constants.toList do
    if count < 50 then
      let t := ci.type
      if t.isConstOf ``False || t.isConstOf ``Empty then
        logInfo m!"{n} : {t}"
        count := count + 1
  logInfo m!"count shown {count}"
