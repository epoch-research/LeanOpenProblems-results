import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command
#eval show CommandElabM Unit from Command.liftTermElabM do
  let env ← getEnv
  for (n, ci) in env.constants.toList do
    if (toString n).contains "lcProof" then logInfo m!"lc {n} : {ci.type}"
    match ci.type with
    | .forallE _ bi body _ =>
      if body.isSort then pure () else
      if body.isConstOf `False then logInfo m!"forallFalse? {n} : {ci.type}"
    | _ => pure ()
