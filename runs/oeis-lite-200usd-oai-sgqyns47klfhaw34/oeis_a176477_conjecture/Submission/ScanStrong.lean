import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command
#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut count := 0
  for (n, ci) in env.constants.toList do
    let t := ci.type
    let s := toString t
    if s.contains "∀ {α : Prop}, α" || s.contains "∀ (α : Prop), α" || s == "False" || s.contains "Nonempty False" then
      logInfo m!"{n} : {t}"
      count := count + 1
  logInfo m!"count {count}"
