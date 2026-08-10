import FormalConjectures.Util.ProblemImports
import Lean
open Lean Meta Elab Command
#eval show CoreM Unit from do
  let env ← getEnv
  for (n, ci) in env.constants.toList do
    let ns := toString n
    if (ns.startsWith "Nat." || ns.startsWith "Chebyshev." || ns.startsWith "Bertrand." || ns.startsWith "FormalConjectures" || ns.startsWith "Counterexamples") &&
       (ns.contains "prime" || ns.contains "Prime" || ns.contains "choose" || ns.contains "factorial" || ns.contains "Chebyshev" || ns.contains "bertrand" || ns.contains "gap" || ns.contains "Gap") then
      IO.println ns
