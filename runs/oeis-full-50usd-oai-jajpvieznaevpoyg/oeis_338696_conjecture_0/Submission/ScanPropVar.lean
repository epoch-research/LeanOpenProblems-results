import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command

partial def endsInLooseBVar (e : Expr) : Bool :=
  match e with
  | .forallE _ _ b _ => endsInLooseBVar b
  | .letE _ _ _ b _ => endsInLooseBVar b
  | .bvar _ => true
  | _ => false

elab "#scan_propvar_allowed" : command => liftCoreM do
  let env ← getEnv
  let allowed := [`propext, `Classical.choice, `Quot.sound]
  let mut count := 0
  for (n, ci) in env.constants.toList do
    if endsInLooseBVar ci.type then
      let axs ← collectAxioms n
      if axs.all (fun a => allowed.contains a) then
        if count < 50 then logInfo m!"PROPVAR {n}: {ci.type} axioms {axs}"
        count := count + 1
  logInfo m!"done {count}"
#scan_propvar_allowed
