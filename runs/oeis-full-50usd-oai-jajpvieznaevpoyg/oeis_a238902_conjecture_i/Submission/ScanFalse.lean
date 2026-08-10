import FormalConjectures.Util.ProblemImports

open Lean Meta Elab Command

#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut count := 0
  for (name, ci) in env.constants.toList do
    let ty := ci.type
    if ty.isConstOf ``False then
      let axs ← collectAxioms name
      let allowed := axs.all (fun a => a == ``propext || a == ``Classical.choice || a == ``Quot.sound)
      if allowed then
        logInfo m!"FALSE DECL {name} axioms {axs}"
        count := count + 1
  logInfo m!"count={count}"
