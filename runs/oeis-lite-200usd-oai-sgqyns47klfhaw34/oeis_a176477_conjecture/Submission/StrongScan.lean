import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command
#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut cnt := 0
  for (n, ci) in env.constants.toList do
    let s := toString ci.type
    if (s.contains "∀ (α : Sort" && s.contains "Nonempty α") ||
       (s.contains "∀ (α : Type" && s.contains "Inhabited α") ||
       (s.contains "∀ {α : Prop}, α") ||
       (s.contains "∀ (P : Prop), P") then
      logInfo m!"{n} : {ci.type}"
      cnt := cnt+1
      if cnt > 100 then break
  logInfo m!"count {cnt}"
