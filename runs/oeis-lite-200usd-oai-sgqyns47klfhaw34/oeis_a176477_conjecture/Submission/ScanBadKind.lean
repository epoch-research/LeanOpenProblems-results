import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command
#eval show CommandElabM Unit from do
  let env ← getEnv
  for (n, ci) in env.constants.toList do
    let ty := ci.type.cleanupAnnotations
    match ty with
    | .forallE _ (.sort .zero) (.bvar 0) _ =>
      let kind := match ci with
        | .axiomInfo _ => "axiom"
        | .defnInfo _ => "defn"
        | .thmInfo _ => "theorem"
        | .opaqueInfo _ => "opaque"
        | .quotInfo _ => "quot"
        | .ctorInfo _ => "ctor"
        | .inductInfo _ => "induct"
        | .recInfo _ => "rec"
      logInfo m!"forallP {n} {kind}"
    | _ => pure ()
