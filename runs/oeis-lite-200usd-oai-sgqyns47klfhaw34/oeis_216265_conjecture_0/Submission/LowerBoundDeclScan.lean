import FormalConjectures.Util.ProblemImports
import Lean
open Lean Meta Elab Command
#eval show CoreM Unit from do
  let env ← getEnv
  for (n, ci) in env.constants.toList do
    let ns := toString n
    if ns.startsWith "Chebyshev." || ns.startsWith "Nat." then
      let ts := toString ci.type
      if (ts.contains "≤" || ts.contains "<") && (ts.contains "theta" || ts.contains "ψ" || ts.contains "π" || ts.contains "primeCounting") && (ns.contains "ge" || ns.contains "le" || ns.contains "lt" || ns.contains "pos" || ns.contains "bound") then
        IO.println s!"{n} : {ts}"
