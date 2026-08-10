import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command

elab "#scan_oracle" : command => liftCoreM do
  let env ← getEnv
  let allowed := [`propext, `Classical.choice, `Quot.sound]
  for (n, ci) in env.constants.toList do
    let t := ci.type
    match t with
    | .forallE _ dom body _ =>
      if dom.isSort && body.hasLooseBVars then
        pure ()
      else pure ()
    | _ => pure ()
  -- use Meta for whnf matching
  Meta.MetaM.run' do
    for (n, ci) in env.constants.toList do
      let t ← whnf ci.type
      if let .forallE _ dom body _ := t then
        let dom ← whnf dom
        if dom == .sort .zero then
          let body := body.instantiate1 (.bvar 0)
          if body == .bvar 0 then
            let axs ← collectAxioms n
            let bad := axs.filter fun a => !(allowed.contains a)
            logInfo m!"oracle-shape {n}: axioms {axs} bad {bad}"
#scan_oracle
