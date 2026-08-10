import FormalConjectures.Util.ProblemImports
open Lean Elab Command

partial def occursBVar (idx : Nat) : Expr → Bool
| .bvar i => i == idx
| .app f a => occursBVar idx f || occursBVar idx a
| .lam _ d b _ => occursBVar idx d || occursBVar (idx+1) b
| .forallE _ d b _ => occursBVar idx d || occursBVar (idx+1) b
| .letE _ t v b _ => occursBVar idx t || occursBVar idx v || occursBVar (idx+1) b
| .mdata _ e => occursBVar idx e
| .proj _ _ e => occursBVar idx e
| _ => false

-- collect forall binders; if a Prop binder's de Bruijn index becomes final conclusion after all binders, print.
partial def scanType (props : List Nat) (depth : Nat) : Expr → Bool
| .forallE _ d b _ =>
    let props' := if d.consumeMData == .sort .zero then depth :: props else props
    scanType props' (depth+1) b
| .mdata _ e => scanType props depth e
| c =>
    match c with
    | .bvar i => props.contains i
    | _ => false

partial def binderCount : Expr → Nat
| .forallE _ _ b _ => 1 + binderCount b
| .mdata _ e => binderCount e
| _ => 0

elab "#arb_prop_scan" : command => do
  let env ← getEnv
  let mut shown := 0
  for (name, ci) in env.constants.toList do
    if name.isInternal then continue
    if scanType [] 0 ci.type.consumeMData then
      try
        let axs ← Lean.collectAxioms name
        let allowed := axs.all fun n => n == `propext || n == `Classical.choice || n == `Quot.sound
        if allowed && binderCount ci.type <= 8 && shown < 300 then
          logInfo m!"{name} : {ci.type} AX={axs}"
          shown := shown + 1
      catch _ => pure ()
  logInfo m!"shown {shown}"
#arb_prop_scan
