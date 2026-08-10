import FormalConjectures.Util.ProblemImports
import Lean
open Lean Meta Elab Command
#eval show CoreM Unit from do
  let env ← getEnv
  for (n, ci) in env.constants.toList do
    let ns := toString n
    if ns.contains "something_that_needs_inverses" || ns.contains "leRecOn" || ns.contains "directSumNeZeroMulEquiv" || ns.endsWith ".do_something" then
      IO.println s!"{n} : {ci.type}"
