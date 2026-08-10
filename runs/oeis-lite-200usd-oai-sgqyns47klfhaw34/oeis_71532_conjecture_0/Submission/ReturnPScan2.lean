import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command

def safe (axs : Array Name) := axs.all fun a => a == ``propext || a == ``Classical.choice || a == ``Quot.sound

partial def finalConcl : Expr → Expr
| .forallE _ _ b _ => finalConcl b
| .mdata _ e => finalConcl e
| e => e

partial def hasBVar (idx : Nat) : Expr → Bool
| .bvar i => i == idx
| .forallE _ d b _ => hasBVar idx d || hasBVar (idx+1) b -- approximate under binder
| .app f a => hasBVar idx f || hasBVar idx a
| .lam _ d b _ => hasBVar idx d || hasBVar (idx+1) b
| .mdata _ e => hasBVar idx e
| .letE _ t v b _ => hasBVar idx t || hasBVar idx v || hasBVar (idx+1) b
| .proj _ _ e => hasBVar idx e
| _ => false

elab "#return_p_scan2" : command => do
  let env ← getEnv
  let mut shown := 0
  for (name, ci) in env.constants.toList do
    if name.isInternal then continue
    let t := ci.type.consumeMData
    -- first binder Prop and final conclusion bvar referring to it (roughly bvar depth num binders-1)
    match t with
    | .forallE _ (.sort .zero) body _ =>
      let c := finalConcl body
      if c.isBVar then
        try
          let axs ← liftTermElabM <| collectAxioms name
          if safe axs then
            logInfo m!"{name} : {t} axs={axs}"
            shown := shown + 1
            if shown > 1000 then break
        catch _ => pure ()
    | _ => pure ()
  logInfo m!"shown {shown}"
#return_p_scan2
