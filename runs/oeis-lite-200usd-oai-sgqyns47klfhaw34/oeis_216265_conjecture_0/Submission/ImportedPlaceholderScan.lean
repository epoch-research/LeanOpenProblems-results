import FormalConjectures.Util.ProblemImports
import Lean
open Lean Meta Elab Command
#eval show CoreM Unit from do
  let names := [`SetTheory.PGame.le_iff_sub_nonneg, `SetTheory.PGame.lt_iff_sub_pos]
  for n in names do
    if let some ci := (← getEnv).find? n then
      IO.println s!"{n}: {ci.type}"
