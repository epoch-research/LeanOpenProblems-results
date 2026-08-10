import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command
#eval show CommandElabM Unit from do
  let env ← getEnv
  for (n,ci) in env.constants.toList do
    if n.isInternal then pure () else
    match ci.type with
    | .const name _ => if name == ``False then logInfo m!"False theorem? {n}" else pure ()
    | _ => pure ()
