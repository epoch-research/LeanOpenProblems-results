import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command
#eval show CommandElabM Unit from Command.liftTermElabM do
  let env ← getEnv
  for (n, ci) in env.constants.toList do
    match ci.type with
    | .forallE _ dom body _ =>
      if dom.isConstOf `True && body.isConstOf `False then logInfo m!"TRUEFALSE {n} : {ci.type}"
      if dom.isAppOf `Nonempty && body.isConstOf `False then logInfo m!"NONEMPTYFALSE {n} : {ci.type}"
    | _ => pure ()
