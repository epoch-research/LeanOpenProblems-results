import FormalConjectures.Util.ProblemImports

open Lean Meta Elab Command

#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut count := 0
  for (n, ci) in env.constants.toList do
    let s := toString ci.type
    if s.contains "∀ {α : Prop}, α" || s.contains "∀ (α : Prop), α" then
      logInfo m!"{n} unsafe {ci.isUnsafe} : {ci.type}"
      count := count + 1
  logInfo m!"count {count}"
