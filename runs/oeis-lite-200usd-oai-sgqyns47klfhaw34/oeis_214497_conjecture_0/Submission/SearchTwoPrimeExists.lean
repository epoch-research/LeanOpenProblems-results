import FormalConjectures.Util.ProblemImports

open Lean Meta Elab Command

elab "#search_two_prime_exists" : command => do
  liftTermElabM do
    let env ← getEnv
    let mut shown := 0
    for (name, ci) in env.constants.toList do
      if ci.isUnsafe then continue
      let s := toString ci.type
      let ns := toString name
      if (s.contains "Nat.Prime" || s.contains ".Prime") && s.contains "∃" &&
         ((s.splitOn "Nat.Prime").length > 2 || (s.splitOn ".Prime").length > 2 || ns.contains "twin" || ns.contains "Twin") then
        if shown < 500 then
          logInfo m!"{name} : {ci.type}"
          shown := shown + 1
    logInfo m!"shown={shown}"

#search_two_prime_exists
