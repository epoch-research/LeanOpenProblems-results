import FormalConjectures.Util.ProblemImports

open Lean Meta Elab Command

#eval show CommandElabM Unit from do
  let env ← getEnv
  let isAllowed (axs : Array Name) : Bool :=
    axs.all (fun a => a == ``propext || a == ``Classical.choice || a == ``Quot.sound)
  for (name, ci) in env.constants.toList do
    let ty := ci.type
    let axs ← collectAxioms name
    if isAllowed axs then
      if ty.isAppOfArity ``Nonempty 1 then
        if ty.getAppArgs[0]!.isConstOf ``False then
          logInfo m!"NONEMPTY FALSE {name} : {ty}"
      match ty with
      | .forallE n d b _ =>
        if d == (.sort .zero) then
          let body := b.instantiate1 (.bvar 0)
          if body == (.bvar 0) then
            logInfo m!"FORALL PROP P {name} : {ty}"
      | _ => pure ()
  logInfo "done"
