import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command
partial def bodyEndsWithVar0 : Expr → Bool
| .forallE _ d b _ => bodyEndsWithVar0 b
| .bvar 0 => true
| _ => false
#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut c := 0
  for (n, ci) in env.constants.toList do
    let ty := ci.type.cleanupAnnotations
    match ty with
    | .forallE _ (.sort .zero) (.bvar 0) _ =>
      logInfo m!"forallP {n} : {ty}"; c:=c+1
    | .forallE _ (.sort .zero) body _ =>
      if body == (.bvar 0) then logInfo m!"forallP2 {n}"
    | _ => pure ()
  logInfo m!"count {c}"
