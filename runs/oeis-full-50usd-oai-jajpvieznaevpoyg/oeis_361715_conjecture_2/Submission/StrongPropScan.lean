import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command Term
#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut c := 0
  for (n, ci) in env.constants.toList do
    if !ci.isUnsafe && c < 50 then
      try
        let fmt ← liftTermElabM <| ppExpr ci.type
        let s := toString fmt
        if (s.contains "∀ (P : Prop), P" || s.contains "(P : Prop) → P" || s.contains "False" && s.contains "∀") then
          logInfo m!"{n} : {s}"
          c := c+1
      catch _ => pure ()
  logInfo m!"count {c}"
