import FormalConjectures.Util.ProblemImports

open Nat Finset

def GoalProp : Prop := ∀ (n : ℕ), n > 0 → n > 0

partial def my_goal_inst_def (u : Unit) : Inhabited (Nonempty GoalProp) :=
  my_goal_inst_def u
