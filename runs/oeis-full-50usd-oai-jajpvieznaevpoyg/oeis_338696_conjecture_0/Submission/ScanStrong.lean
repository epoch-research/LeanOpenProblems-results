import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command

partial def isForallPropToPropVar (e : Expr) : Bool :=
  match e with
  | .forallE _ d b _ =>
      if d == .sort .zero then
        match b with
        | .bvar 0 => true
        | _ => isForallPropToPropVar b
      else isForallPropToPropVar b
  | _ => false

elab "#scan_strong_allowed" : command => liftCoreM do
  let env ← getEnv
  let allowed := [`propext, `Classical.choice, `Quot.sound]
  let mut count := 0
  for (n, ci) in env.constants.toList do
    if isForallPropToPropVar ci.type then
      let axs ← collectAxioms n
      if axs.all (fun a => allowed.contains a) then
        logInfo m!"STRONG {n}: {ci.type} axioms {axs}"
        count := count + 1
  logInfo m!"done {count}"
#scan_strong_allowed
