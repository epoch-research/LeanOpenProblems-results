import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command
#eval show CommandElabM Unit from do
  let env ← getEnv
  for (name, ci) in env.constants.toList do
    let ns := toString name
    let s := toString ci.type
    if (s.contains "descFactorial" || s.contains "ascFactorial" || s.contains "primeFactors" || s.contains "factorization" || s.contains "choose") &&
       (s.contains "Nat.Prime" || s.contains "Prime") && (s.contains "∃" || s.contains "≤" || s.contains "<") then
      if !(ns.contains "Polynomial" || ns.contains "Ring" || ns.contains "Ideal") then
        logInfo m!"{name} : {ci.type}"
