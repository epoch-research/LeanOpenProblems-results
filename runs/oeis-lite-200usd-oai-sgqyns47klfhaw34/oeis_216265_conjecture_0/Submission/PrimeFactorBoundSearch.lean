import FormalConjectures.Util.ProblemImports
import Lean
open Lean Meta Elab Command
#eval show CoreM Unit from do
  let env ← getEnv
  for (n, ci) in env.constants.toList do
    let ns := toString n
    if (ns.startsWith "Nat." || ns.startsWith "Int.") && (ns.contains "primeFactor" || ns.contains "PrimeFactor" || ns.contains "factorization" || ns.contains "minFac" || ns.contains "maxPrime") then
      let ts := toString ci.type
      if ts.contains "≤" || ts.contains "<" || ts.contains "∣" || ts.contains "Prime" then
        IO.println s!"{n} : {ts}"
