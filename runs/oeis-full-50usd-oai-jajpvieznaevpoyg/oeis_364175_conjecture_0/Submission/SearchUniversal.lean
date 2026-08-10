import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command
#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut c := 0
  for (n, ci) in env.constants.toList do
    let t := ci.type
    let s := toString t
    if s.contains "∀ (P : Prop), P" || s.contains "False" then
      logInfo m!"{n} : {t}"
      c := c + 1
      if c > 100 then break
  logInfo m!"count {c}"
