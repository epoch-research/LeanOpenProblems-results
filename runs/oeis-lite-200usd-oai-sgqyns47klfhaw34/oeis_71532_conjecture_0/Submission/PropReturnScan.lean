import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command

partial def conclWithDepth : Nat → Expr → Option Nat
| d, .forallE _ _ b _ => conclWithDepth (d+1) b
| d, .bvar i => some i
| _, _ => none

/-- If first binder is Prop and final conclusion is that first binder, return true. -/
def firstPropReturns : Expr → Bool
| .forallE _ (.sort .zero) body _ =>
    match conclWithDepth 1 body with
    | some i => i == 0 -- maybe wrong due bvar shifts; print all below
    | none => false
| _ => false

elab "#prop_return_scan" : command => do
  let env ← getEnv
  let mut shown := 0
  for (name, ci) in env.constants.toList do
    if name.isInternal then continue
    let t := ci.type.consumeMData
    match t with
    | .forallE _ (.sort .zero) body _ =>
      let rec findConcl : Expr → Expr
        | .forallE _ _ b _ => findConcl b
        | e => e
      let c := findConcl body
      if c.isBVar then
        try
          let axs ← collectAxioms name
          let safe := axs.all (fun a => a == ``propext || a == ``Classical.choice || a == ``Quot.sound)
          if safe then
            logInfo m!"{name} : {t} concl={c} axs={axs}"
            shown := shown + 1
            if shown > 300 then break
        catch _ => pure ()
    | _ => pure ()
  logInfo m!"shown {shown}"
#prop_return_scan
