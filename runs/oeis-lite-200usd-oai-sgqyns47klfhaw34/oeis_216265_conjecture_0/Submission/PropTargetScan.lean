import FormalConjectures.Util.ProblemImports
import Lean
open Lean Meta Elab Command
#eval show CoreM Unit from do
  let env ← getEnv
  for (n, ci) in env.constants.toList do
    let ts := toString ci.type
    if ts.contains "∀ (P : Prop), P" || ts.contains "forall (P : Prop), P" || ts.contains "Nonempty False" then
      IO.println s!"{n} : {ts}"
