import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command

partial def hasLooseBVarPropResult : Expr → Bool
| .forallE _ d b _ => hasLooseBVarPropResult b
| .bvar _ => true
| _ => false

#eval show CommandElabM Unit from do
  let env ← getEnv
  let allowed (axs : Array Name) : Bool := axs.all (fun a => a == ``propext || a == ``Classical.choice || a == ``Quot.sound)
  let mut count := 0
  for (name, ci) in env.constants.toList do
    if name.isInternal then continue
    let axs ← collectAxioms name
    if allowed axs && hasLooseBVarPropResult ci.type then
      logInfo m!"SUSP {name} : {ci.type} axioms {axs}"
      count := count + 1
      if count > 200 then break
  logInfo m!"done {count}"
