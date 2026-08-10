import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command
#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut found := 0
  for (n, ci) in env.constants.toList do
    let s := toString (← Meta.ppExpr ci.type)
    let cond := (s.contains "∀ (P : Prop), P") || (s.contains "∀ {P : Prop}, P") ||
       (s.contains "Nonempty False") || (s == "False") ||
       ((s.contains "∀ (α : Sort") && (s.contains "Nonempty α"))
    if cond then
      logInfo m!"{n} : {s}"
      found := found + 1
  logInfo m!"found {found}"
