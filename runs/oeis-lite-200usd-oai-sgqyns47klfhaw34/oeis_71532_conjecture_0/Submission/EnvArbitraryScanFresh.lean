import FormalConjectures.Util.ProblemImports
import Lean
open Lean Meta Elab Command

partial def hasPropReturn (e : Expr) : MetaM Bool := do
  let e ← whnf e
  match e with
  | .forallE _ d b _ =>
      if d == .sort .zero then
        withLocalDeclD `P d fun x => do
          let body := b.instantiate1 x
          let body ← whnf body
          -- type ∀ P : Prop, P or ∀ P, ¬¬P etc: print if body contains bound x as whole target prop
          return body == x
      else
        withLocalDeclD `x d fun x => hasPropReturn (b.instantiate1 x)
  | _ => return false

#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut count := 0
  for (n, ci) in env.constants.toList do
    if n.isInternal then continue
    try
      if (← liftTermElabM <| hasPropReturn ci.type) then
        let axs ← collectAxioms n
        logInfo m!"ARB {n} : {ci.type} axioms {axs.toList}"
        count := count + 1
        if count > 100 then break
    catch _ => pure ()
  logInfo m!"done {count}"
