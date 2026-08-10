import FormalConjectures.Util.ProblemImports

open Lean Meta Elab Command

elab "#prime_focused" : command => do
  liftTermElabM do
    let env ← getEnv
    let needles := ["+ 2", "+ 1", "succ", "next", "prev", "twin", "gap", "consecutive", "Prime (", "Nat.Prime"]
    let mut shown := 0
    for (name, ci) in env.constants.toList do
      let ns := toString name
      let s := toString ci.type
      if (s.contains "Nat.Prime" || ns.contains "Prime" || ns.contains "prime") &&
         ((s.contains "+ 2" || s.contains "+ 1" || s.contains "succ" || ns.contains "succ" || ns.contains "twin" || ns.contains "gap" || ns.contains "consecutive") ||
          (s.contains "∃" && s.contains "Nat.Prime" && s.contains "Nat.Prime")) then
        if shown < 1000 then
          logInfo m!"{name} : {ci.type}"
          shown := shown + 1
    logInfo m!"shown {shown}"

#prime_focused
