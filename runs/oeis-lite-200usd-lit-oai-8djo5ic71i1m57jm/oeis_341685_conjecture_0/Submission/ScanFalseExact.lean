import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command
#eval show CommandElabM Unit from Command.liftTermElabM do
  let env ← getEnv
  for (n, ci) in env.constants.toList do
    if ci.type.isConstOf `False then logInfo m!"FALSE {n} : {ci.type}"
