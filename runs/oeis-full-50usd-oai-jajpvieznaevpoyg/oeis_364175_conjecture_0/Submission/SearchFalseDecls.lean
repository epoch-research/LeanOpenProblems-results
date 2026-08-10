import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command
#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut count := 0
  for (n, ci) in env.constants.toList do
    let t := ci.type
    if t.isConstOf ``False then
      logInfo m!"FALSE DECL {n} : {t}"
      count := count + 1
      if count > 50 then break
  logInfo m!"count {count}"
