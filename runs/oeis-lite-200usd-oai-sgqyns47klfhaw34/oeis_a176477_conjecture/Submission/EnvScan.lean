import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command

#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut count := 0
  for (n, ci) in env.constants.toList do
    if count < 200 then
      let t := ci.type
      let s := toString t
      if s == "False" || s.contains "∀ (P : Prop), P" || s.contains "∀ P, P" || s.contains "False →" || s.contains "Nonempty False" || s.contains "Empty False" then
        logInfo m!"{n} : {t}"
        count := count + 1
  logInfo m!"count {count}"
