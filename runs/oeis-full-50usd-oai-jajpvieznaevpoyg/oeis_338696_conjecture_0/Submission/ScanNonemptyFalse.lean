import FormalConjectures.Util.ProblemImports

open Lean Meta Elab Command

elab "#scan_nf" : command => liftTermElabM do
  let target1 ← Elab.Term.elabType (← `(Nonempty False))
  let target2 ← Elab.Term.elabType (← `(Inhabited False))
  let env ← getEnv
  let mut count := 0
  for (n, ci) in env.constants.toList do
    if ci.type == target1 || ci.type == target2 then
      logInfo m!"decl: {n} : {ci.type}, unsafe={ci.isUnsafe}"
      count := count + 1
  logInfo m!"count {count}"
#scan_nf
