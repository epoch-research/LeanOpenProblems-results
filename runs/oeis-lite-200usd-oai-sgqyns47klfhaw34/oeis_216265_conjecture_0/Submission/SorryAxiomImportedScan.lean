import FormalConjectures.Util.ProblemImports
import Lean
open Lean Meta Elab Command
#eval show CoreM Unit from do
  let env ← getEnv
  let mut num := 0
  for (n, ci) in env.constants.toList do
    -- only check theorem/def values for direct constants; full transitive axioms is too slow
    match ci.value? with
    | some v =>
      if v.hasConst `sorryAx then
        IO.println s!"direct sorryAx in {n} : {ci.type}"
        num := num + 1
    | none => pure ()
  IO.println s!"direct count {num}"
