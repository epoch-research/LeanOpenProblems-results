import FormalConjectures.Util.ProblemImports
import Lean
open Lean Meta Elab Command
#eval show CoreM Unit from do
  let env ← getEnv
  for (n, ci) in env.constants.toList do
    let ns := toString n
    if ns.contains "eventually" || ns.contains "Eventually" || ns.contains "Tendsto" || ns.contains "frequently" || ns.contains "Frequently" then
      let ts := toString ci.type
      if ts.contains "Prime" || ts.contains "prime" || ts.contains "primeCounting" then
        IO.println s!"{n} : {ts}"
