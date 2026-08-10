import FormalConjectures.Util.ProblemImports

open Lean Meta Elab Command

elab "#scan_magic" : command => liftTermElabM do
  let target ← Elab.Term.elabType (← `(∀ p : Prop, p))
  let env ← getEnv
  let mut count := 0
  for (n, ci) in env.constants.toList do
    try
      if (← isDefEq ci.type target) then
        logInfo m!"magic decl: {n} : {ci.type}"
        count := count + 1
        if count > 20 then break
    catch _ => pure ()
  logInfo m!"count {count}"

#scan_magic
