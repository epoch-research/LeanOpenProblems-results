import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command Term
#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut c := 0
  for (n, ci) in env.constants.toList do
    let ns := toString n
    if c < 100 && (ns.contains "ZMod" || ns.contains "Prime" || ns.contains "Subsingleton") then
      try
        let fmt ← liftTermElabM <| ppExpr ci.type
        let s := toString fmt
        if (s.contains "Subsingleton (ZMod" || s.contains "ZMod" && s.contains "= 1" || s.contains "Nat.Prime" && s.contains "= 1") then
          logInfo m!"{n} : {s}"
          c := c+1
      catch _ => pure ()
  logInfo m!"count {c}"
