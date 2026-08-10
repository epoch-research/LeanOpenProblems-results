import FormalConjectures.Util.ProblemImports

open Lean Meta Elab Command

elab "#scan_bad_axioms" : command => liftTermElabM do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let env ← getEnv
  let mut count := 0
  for (n, ci) in env.constants.toList do
    if !ci.isUnsafe then
      let ax ← collectAxioms n
      let bad := ax.toList.filter (fun a => !allowed.contains a)
      if !bad.isEmpty then
        logInfo m!"{n}: bad axioms {bad} type {ci.type}"
        count := count + 1
        if count > 100 then break
  logInfo m!"count {count}"

set_option maxHeartbeats 1000000 in
#scan_bad_axioms
