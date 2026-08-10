import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command
partial def finalConcl : Expr → Expr | .forallE _ _ b _ => finalConcl b | e => e
elab "#arb_cert_scan_fast" : command => do
  let env ← getEnv
  let mut shown := 0
  for (name, ci) in env.constants.toList do
    if name.isInternal then continue
    let ns := toString name
    unless (ns.contains "Sat" || ns.contains "Decidable" || ns.contains "of_" || ns.contains "refute" || ns.contains "proof" || ns.contains "Proof" || ns.contains "Erased") do continue
    let t := ci.type.consumeMData
    let c := finalConcl t
    if c.isBVar then
      try
        let axs ← collectAxioms name
        let safe := axs.all (fun a => a == ``propext || a == ``Classical.choice || a == ``Quot.sound)
        if safe then
          logInfo m!"{name} : {t} axs={axs}"
          shown := shown + 1
      catch _ => pure ()
  logInfo m!"shown {shown}"
#arb_cert_scan_fast
