import FormalConjectures.Util.ProblemImports

open Lean Meta Elab Command

elab "#prime_gap_names" : command => do
  liftTermElabM do
    let env ← getEnv
    let mut shown := 0
    for (name, ci) in env.constants.toList do
      let ns := toString name
      let s := toString ci.type
      if (ns.contains "primeGap" || ns.contains "nth_prime" || ns.contains "nthPrime" || ns.contains "nth_prime" || s.contains "primeGap" || s.contains "nth Nat.Prime" || s.contains "Nat.Prime" && s.contains "nth") then
        if shown < 500 then logInfo m!"{name} : {ci.type}"
        shown := shown + 1
    logInfo m!"shown={shown}"

#prime_gap_names
