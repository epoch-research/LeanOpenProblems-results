import FormalConjectures.Util.ProblemImports
import Qq
open Lean Meta Elab Command Qq
#eval show CommandElabM Unit from do
  let env ← getEnv
  let target : Q(Prop) := q(∀ P : Prop, P)
  let mut shown := 0
  for (n, ci) in env.constants.toList do
    try
      if (← liftTermElabM <| Meta.isDefEq ci.type target) then
        logInfo m!"FOUND exact {n}"
        shown := shown+1
    catch _ => pure ()
  logInfo m!"done {shown}"
