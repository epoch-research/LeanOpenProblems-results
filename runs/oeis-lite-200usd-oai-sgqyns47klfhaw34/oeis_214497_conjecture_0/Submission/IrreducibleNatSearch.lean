import FormalConjectures.Util.ProblemImports

open Lean Meta Elab Command

elab "#irreducible_nat_search" : command => do
  liftTermElabM do
    let env ← getEnv
    let mut shown := 0
    for (name, ci) in env.constants.toList do
      let ns := toString name
      let s := toString ci.type
      if (s.contains "Irreducible" || s.contains "Nat.Prime" || ns.contains "irreducible" || ns.contains "Prime") &&
         (s.contains "∀" || s.contains "->" || s.contains "→") &&
         (s.contains "Nat" || s.contains "ℕ" || ns.contains "Nat") then
        if shown < 500 then
          logInfo m!"{name} : {ci.type}"
          shown := shown + 1
    logInfo m!"shown={shown}"

#irreducible_nat_search
