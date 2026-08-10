import FormalConjectures.Util.ProblemImports
import Lean
open Lean Meta Elab Command
#eval show CoreM Unit from do
  let env ← getEnv
  for (n, ci) in env.constants.toList do
    let ns := toString n
    if ns.contains "Bunyakovsky" || ns.contains "Schinzel" || ns.contains "Cramer" ||
       ns.contains "Legendre" || ns.contains "Oppermann" || ns.contains "Nagura" ||
       ns.contains "Dusart" || ns.contains "primeGap" || ns.contains "PrimeGap" ||
       ns.contains "Conjecture" || ns.contains "conjecture" || ns.contains "ShortInterval" then
      IO.println s!"{n} : {ci.type}"
