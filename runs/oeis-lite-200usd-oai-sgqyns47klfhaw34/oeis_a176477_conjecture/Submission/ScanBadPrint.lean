import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command
#eval show CommandElabM Unit from do
  let env ← getEnv
  for (n, ci) in env.constants.toList do
    let ty := ci.type.cleanupAnnotations
    match ty with
    | .forallE _ (.sort .zero) (.bvar 0) _ =>
      logInfo m!"forallP {n} info={repr ci}"
    | _ => pure ()
