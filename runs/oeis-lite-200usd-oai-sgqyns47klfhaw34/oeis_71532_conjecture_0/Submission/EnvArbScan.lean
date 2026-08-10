import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command

/-- Detect shape forall (P : Prop), ... -> P approximately. -/
def returnsBoundProp : Expr → Bool
| .forallE _ (.sort .zero) body _ =>
  let rec go : Expr → Bool
  | .forallE _ _ b _ => go b
  | .bvar 0 => true
  | _ => false
  go body
| _ => false

elab "#arb_scan" : command => do
  let env ← getEnv
  let mut shown := 0
  for (name, ci) in env.constants.toList do
    if name.isInternal then continue
    let type := ci.type.consumeMData
    if returnsBoundProp type then
      try
        let axs ← collectAxioms name
        let safe := axs.all (fun a => a == ``propext || a == ``Classical.choice || a == ``Quot.sound)
        if safe then
          shown := shown+1
          logInfo m!"{name} : {type} axioms={axs}"
      catch _ => pure ()
  logInfo m!"shown {shown}"
#arb_scan
