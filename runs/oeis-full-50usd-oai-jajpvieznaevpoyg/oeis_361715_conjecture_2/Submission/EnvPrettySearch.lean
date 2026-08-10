import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command Term

#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut found := 0
  for (n, ci) in env.constants.toList do
    let ns := toString n
    if found < 200 && (ns.contains "choose" || ns.contains "Choose" || ns.contains "lucas" || ns.contains "Lucas" || ns.contains "ModEq" || ns.contains "padic" || ns.contains "factorization") then
      try
        let fmt ← liftTermElabM <| ppExpr ci.type
        let str := toString fmt
        if (str.contains "Prime" || str.contains "prime") &&
           (str.contains "ModEq" || str.contains "ZMOD" || str.contains "∣" || str.contains "factorization") then
          logInfo m!"{n} : {str}"
          found := found + 1
      catch _ => pure ()
  logInfo m!"found {found}"
