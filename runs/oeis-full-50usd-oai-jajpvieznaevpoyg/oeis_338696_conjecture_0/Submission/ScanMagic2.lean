import FormalConjectures.Util.ProblemImports

open Lean Meta Elab Command

elab "#scan_magic2" : command => liftTermElabM do
  let t1 ← Elab.Term.elabType (← `(∀ {p : Prop}, p))
  let t2 ← Elab.Term.elabType (← `(∀ p : Prop, p))
  let targets := #[t1, t2]
  let env ← getEnv
  for (n, ci) in env.constants.toList do
    for target in targets do
      try
        if (← isDefEq ci.type target) then
          logInfo m!"magic decl: {n} : {ci.type}, unsafe={ci.isUnsafe}"
      catch _ => pure ()
#scan_magic2
