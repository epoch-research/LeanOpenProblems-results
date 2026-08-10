import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command Term
#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut c := 0
  for (n, ci) in env.constants.toList do
    let ns := toString n
    if c < 200 && (ns.contains "ModEq" || ns.contains "modEq" || ns.contains "dvd" || ns.contains "Dvd") then
      try
        let fmt ← liftTermElabM <| ppExpr ci.type
        let s := toString fmt
        if s.contains "Int.ModEq" || s.contains "ZMOD" || s.contains "≡" then
          if s.contains "∀" && (s.contains "True" || s.contains "0" || s.contains "∣") then
            logInfo m!"{n} : {s}"
            c := c+1
      catch _ => pure ()
  logInfo m!"count {c}"
