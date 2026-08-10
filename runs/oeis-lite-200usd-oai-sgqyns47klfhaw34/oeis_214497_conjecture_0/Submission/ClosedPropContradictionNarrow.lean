import FormalConjectures.Util.ProblemImports

open Lean Meta Elab Command

def allowedAxiomName (n : Name) : Bool :=
  n == `propext || n == `Classical.choice || n == `Quot.sound

#eval show CommandElabM Unit from do
  let env ← getEnv
  let targets := ["Subsingleton Prop", "Unique Prop", "False", "IsEmpty True", "IsEmpty PUnit"]
  for (n, ci) in env.constants.toList do
    let s := toString ci.type
    if targets.any (fun t => s == t) then
      let axs ← liftCoreM <| collectAxioms n
      if axs.all allowedAxiomName then
        logInfo m!"FOUND {n} axs={axs} : {ci.type}"
