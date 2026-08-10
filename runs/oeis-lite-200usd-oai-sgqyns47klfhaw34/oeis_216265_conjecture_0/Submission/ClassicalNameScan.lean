import FormalConjectures.Util.ProblemImports
import Lean
open Lean Meta Elab Command
#eval show CoreM Unit from do
  let env ← getEnv
  for (n, ci) in env.constants.toList do
    let ns := toString n
    if ns.startsWith "Classical." && (ns.contains "prop" || ns.contains "Prop" || ns.contains "complete" || ns.contains "choice" || ns.contains "dec") then
      IO.println s!"{n} : {ci.type}"
