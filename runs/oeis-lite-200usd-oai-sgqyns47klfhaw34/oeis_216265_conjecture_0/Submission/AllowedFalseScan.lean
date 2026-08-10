import FormalConjectures.Util.ProblemImports
import Lean
open Lean Meta Elab Command
#eval show CoreM Unit from do
  let env ← getEnv
  let mut count := 0
  for (n, ci) in env.constants.toList do
    let ts := toString ci.type
    if ts == "False" then
      IO.println s!"{n} : False"
      count := count + 1
  IO.println s!"count={count}"
