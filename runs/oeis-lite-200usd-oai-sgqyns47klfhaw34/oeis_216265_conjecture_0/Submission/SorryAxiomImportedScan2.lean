import FormalConjectures.Util.ProblemImports
import Lean
open Lean Meta Elab Command

def containsConst (e : Expr) (target : Name) : Bool :=
  e.foldConsts false (fun n acc => acc || n == target)

#eval show CoreM Unit from do
  let env ← getEnv
  let mut num := 0
  for (n, ci) in env.constants.toList do
    let ns := toString n
    if ns.startsWith "Nat." || ns.startsWith "Chebyshev." || ns.startsWith "SetTheory.PGame." || ns.startsWith "Mathlib." || ns.startsWith "FormalConjectures" then
      match ci.value? with
      | some v =>
        if containsConst v `sorryAx then
          IO.println s!"direct sorryAx in {n} : {ci.type}"
          num := num + 1
      | none => pure ()
  IO.println s!"direct count {num}"
