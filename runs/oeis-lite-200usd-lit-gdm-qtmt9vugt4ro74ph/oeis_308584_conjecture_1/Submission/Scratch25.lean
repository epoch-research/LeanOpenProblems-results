import FormalConjectures.Util.ProblemImports

open Nat Finset

def GoalProp : Prop := ∀ (n : ℕ), n > 0 → n > 0

partial def get_nonempty (f : GoalProp) (u : Unit) : Nonempty GoalProp :=
  ⟨f⟩
