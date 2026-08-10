import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command

partial def conclusion : Expr → Expr
| .forallE _ _ b _ => conclusion b
| e => e

def isSubsingletonConcl : Expr → Bool
| .app (.const n _) _ => n == ``Subsingleton
| _ => false

elab "#subsingle_concl" : command => do
  let env ← getEnv
  let mut shown := 0
  for (name, ci) in env.constants.toList do
    if name.isInternal then continue
    let c := conclusion ci.type.consumeMData
    if isSubsingletonConcl c then
      try
        let axs ← collectAxioms name
        let safe := axs.all (fun a => a == ``propext || a == ``Classical.choice || a == ``Quot.sound)
        if safe then
          shown := shown+1
          logInfo m!"{name} : {ci.type}"
          if shown > 300 then break
      catch _ => pure ()
  logInfo m!"shown {shown}"
#subsingle_concl
