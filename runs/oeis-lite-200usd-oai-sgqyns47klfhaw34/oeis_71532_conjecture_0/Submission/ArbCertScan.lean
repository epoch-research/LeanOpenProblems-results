import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command

/-- Get final conclusion ignoring forall binders. -/
partial def finalConcl : Expr → Expr
| .forallE _ _ b _ => finalConcl b
| e => e

elab "#arb_cert_scan" : command => do
  let env ← getEnv
  let mut shown := 0
  for (name, ci) in env.constants.toList do
    if name.isInternal then continue
    let t := ci.type.consumeMData
    -- show safe declarations whose first explicit/implicit binder is Prop and conclusion is a bound var
    let s := toString t
    if s.contains "{p : Prop}" || s.contains "(p : Prop)" then
      let c := finalConcl t
      if c.isBVar then
        try
          let axs ← collectAxioms name
          let safe := axs.all (fun a => a == ``propext || a == ``Classical.choice || a == ``Quot.sound)
          if safe then
            logInfo m!"{name} : {t} axs={axs}"
            shown := shown + 1
            if shown > 500 then break
        catch _ => pure ()
  logInfo m!"shown {shown}"
#arb_cert_scan
