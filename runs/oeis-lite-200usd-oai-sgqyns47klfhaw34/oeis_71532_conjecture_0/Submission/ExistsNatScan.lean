import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command
partial def finalConcl : Expr → Expr | .forallE _ _ b _ => finalConcl b | e => e

def isExistsNat : Expr → Bool
| .app (.app (.const ``Exists _) (.const ``Nat _)) _ => true
| _ => false

elab "#exists_nat_scan" : command => do
  let env ← getEnv
  let mut shown := 0
  for (name, ci) in env.constants.toList do
    if name.isInternal then continue
    let c := finalConcl ci.type.consumeMData
    if isExistsNat c then
      try
        let axs ← collectAxioms name
        let safe := axs.all (fun a => a == ``propext || a == ``Classical.choice || a == ``Quot.sound)
        if safe then
          logInfo m!"{name} : {ci.type} axs={axs}"
          shown := shown + 1
          if shown > 300 then break
      catch _ => pure ()
  logInfo m!"shown {shown}"
#exists_nat_scan
