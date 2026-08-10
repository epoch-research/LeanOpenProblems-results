import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command

elab "#strong_search" : command => do
  let env ← getEnv
  let patterns := #["Subsingleton ℕ", "0 = 1", "1 = 0", "False", "∀ (α : Sort", "∀ {α : Sort", "α"]
  let mut shown := 0
  for (n, ci) in env.constants.toList do
    match ci with
    | .thmInfo ti =>
      let fmt ← liftTermElabM <| ppExpr ti.type
      let s := toString fmt
      if (s.contains "Subsingleton ℕ" || s.contains "0 = 1" || s.contains "1 = 0" || s == "False") then
        logInfo m!"THM {n} : {fmt}"
        shown := shown + 1
    | .defnInfo di =>
      let fmt ← liftTermElabM <| ppExpr di.type
      let s := toString fmt
      if (s.contains "Subsingleton ℕ" || s.contains "0 = 1" || s.contains "1 = 0" || s == "False") then
        logInfo m!"DEF {n} : {fmt}"
        shown := shown + 1
    | _ => pure ()
  logInfo m!"shown {shown}"
#strong_search
