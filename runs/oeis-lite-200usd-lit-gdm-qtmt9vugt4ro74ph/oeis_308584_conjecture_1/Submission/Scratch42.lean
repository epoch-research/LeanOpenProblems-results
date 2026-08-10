import FormalConjectures.Util.ProblemImports

open Nat Finset

def GoalProp : Prop := ∀ (n : ℕ), n > 0 → n > 0

partial def loop_forever (h_not : Nonempty GoalProp → False) : GoalProp :=
  loop_forever h_not

#print axioms loop_forever
