import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command
#eval show CommandElabM Unit from do
  let env ← getEnv
  for (name, ci) in env.constants.toList do
    match ci.type with
    | .forallE _ (.sort .zero) body _ =>
      let expected := mkApp (mkConst ``Nonempty [0]) (.bvar 0)
      if body == expected then logInfo m!"FOUND {name} : {ci.type}"
    | _ => pure ()
  logInfo "done"
