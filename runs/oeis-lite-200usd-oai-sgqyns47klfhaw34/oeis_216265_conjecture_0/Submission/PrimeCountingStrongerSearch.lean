import FormalConjectures.Util.ProblemImports
import Lean
open Lean Meta Elab Command
#eval show CoreM Unit from do
  let env ← getEnv
  for (n, ci) in env.constants.toList do
    let ns := toString n
    if (ns.startsWith "Nat." || ns.startsWith "Chebyshev.") && (ns.contains "primeCounting" || ns.contains "count" || ns.contains "nth") then
      let ts := toString ci.type
      if ts.contains "≤" || ts.contains "<" || ts.contains "∃" || ts.contains "Surjective" || ts.contains "Tendsto" then
        IO.println s!"{n} : {ts}"
