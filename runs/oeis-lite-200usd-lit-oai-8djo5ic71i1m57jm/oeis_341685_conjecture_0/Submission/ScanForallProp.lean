import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command
#eval show CommandElabM Unit from Command.liftTermElabM do
  let env ← getEnv
  for (n, ci) in env.constants.toList do
    let t := ci.type
    match t with
    | .forallE nm (.sort .zero) (.bvar 0) bi => logInfo m!"ARB {n} : {t}"
    | _ => pure ()
