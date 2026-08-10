import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command

elab "#scan_false_allowed" : command => liftCoreM do
  let env ← getEnv
  let allowed := [`propext, `Classical.choice, `Quot.sound]
  let mut count := 0
  for (n, ci) in env.constants.toList do
    let t := ci.type
    if t.isConstOf ``False then
      let axs ← collectAxioms n
      let bad := axs.filter fun a => !(allowed.contains a)
      if bad.isEmpty then
        logInfo m!"ALLOWED FALSE {n}: axioms {axs}"
        count := count + 1
      else if !(axs.contains ``sorryAx) && !(axs.contains ``lcProof) then
        logInfo m!"false {n}: axioms {axs} bad {bad}"
  logInfo m!"done count {count}"

#scan_false_allowed
