import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command
#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut c := 0
  for (n, ci) in env.constants.toList do
    let ns := toString n
    if ns.startsWith "Nat." || ns.contains "prime" || ns.contains "Prime" || ns.contains "Bertrand" then
      let s := toString ci.type
      if (s.contains "nth Nat.Prime" || s.contains "Nat.nth Nat.Prime" || s.contains "nth Prime" || s.contains "primeGap" || s.contains "Nat.Primes") &&
         (s.contains "≤" || s.contains "<" || s.contains "∃" || s.contains "∀") then
        logInfo m!"{n} : {ci.type}"
        c := c + 1
        if c > 400 then break
  logInfo m!"count {c}"
