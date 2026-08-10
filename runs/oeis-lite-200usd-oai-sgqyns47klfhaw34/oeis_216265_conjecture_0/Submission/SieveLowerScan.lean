import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command
#eval show CommandElabM Unit from do
  let env ← getEnv
  for (name, ci) in env.constants.toList do
    let ns := toString name
    let s := toString ci.type
    if (ns.contains "smooth" || ns.contains "rough" || ns.contains "Sieve" || ns.contains "sieve" || ns.contains "coprime" || ns.contains "Coprime" || ns.contains "totient" || ns.contains "primesBelow") &&
       (s.contains "≤" || s.contains "<" || s.contains "card" || s.contains "∃") then
      if ns.startsWith "Nat." || ns.contains "Sieve" || ns.contains "smooth" || ns.contains "rough" || ns.contains "totient" then
        logInfo m!"{name} : {ci.type}"
