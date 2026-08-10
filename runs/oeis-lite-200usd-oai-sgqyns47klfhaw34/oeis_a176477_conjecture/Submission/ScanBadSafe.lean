import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command
#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut c := 0
  for (n, ci) in env.constants.toList do
    let ty := ci.type.cleanupAnnotations
    let safe := ci.safety
    match ty with
    | .forallE _ (.sort .zero) (.bvar 0) _ =>
      logInfo m!"forallP {n} safety={safe}"; c:=c+1
    | _ => pure ()
  logInfo m!"count {c}"
