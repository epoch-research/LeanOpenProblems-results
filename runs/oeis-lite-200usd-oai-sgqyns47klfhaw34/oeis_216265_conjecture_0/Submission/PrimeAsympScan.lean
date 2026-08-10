import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command
#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut c := 0
  for (n, ci) in env.constants.toList do
    let ns := toString n
    if ns.startsWith "Chebyshev." || ns.startsWith "Nat." || ns.contains "Prime" || ns.contains "prime" then
      let s := toString ci.type
      if (s.contains "primeCounting" || s.contains "theta" || s.contains "ψ" || s.contains "Nat.Prime" || s.contains "primesBelow") &&
         (s.contains "IsLittleO" || s.contains "=o" || s.contains "IsBigO" || s.contains "=O" || s.contains "Tendsto" || s.contains "Eventually" || s.contains "∀ᶠ" || s.contains "Summable" || s.contains "∑") then
        logInfo m!"{n} : {ci.type}"
        c := c+1
        if c > 250 then break
  logInfo m!"count {c}"
