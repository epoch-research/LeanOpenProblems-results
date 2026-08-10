import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command

partial def hasConst (n : Name) : Expr → Bool
| .const m _ => m == n
| .app f a => hasConst n f || hasConst n a
| .lam _ t b _ => hasConst n t || hasConst n b
| .forallE _ t b _ => hasConst n t || hasConst n b
| .letE _ t v b _ => hasConst n t || hasConst n v || hasConst n b
| .mdata _ e => hasConst n e
| .proj _ _ e => hasConst n e
| _ => false

elab "#contr_scan2" : command => do
  let env ← getEnv
  let mut shown := 0
  for (name, ci) in env.constants.toList do
    if name.isInternal then continue
    let type := ci.type.consumeMData
    if hasConst ``Nat type && (hasConst ``Subsingleton type || hasConst ``IsEmpty type || hasConst ``False type) then
      try
        let axs ← collectAxioms name
        let safe := axs.all (fun a => a == ``propext || a == ``Classical.choice || a == ``Quot.sound)
        if safe then
          shown := shown + 1
          logInfo m!"{name} : {type} axioms={axs}"
          if shown > 200 then break
      catch _ => pure ()
  logInfo m!"shown {shown}"
#contr_scan2
