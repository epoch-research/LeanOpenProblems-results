import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command
#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut c := 0
  for (n, ci) in env.constants.toList do
    let ns := toString n
    if (ns.startsWith "Nat." || ns.contains "Factorial" || ns.contains "factorial" || ns.contains "choose" || ns.contains "desc" || ns.contains "asc" || ns.contains "Sylvester" || ns.contains "Bertrand") then
      let s := toString ci.type
      if s.contains "Nat.Prime" && s.contains "∣" && (s.contains "factorial" || s.contains "choose" || s.contains "descFactorial" || s.contains "ascFactorial" || s.contains "Finset.prod") then
        logInfo m!"{n} : {ci.type}"
        c := c+1
        if c > 500 then break
  logInfo m!"count {c}"
