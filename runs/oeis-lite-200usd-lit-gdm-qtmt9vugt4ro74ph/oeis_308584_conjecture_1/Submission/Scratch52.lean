import FormalConjectures.Util.ProblemImports

open Nat Finset

def GoalProp : Prop := ∀ (n : ℕ), n > 0 → n > 0

mutual
  partial def safe_goal_nonempty (u : Unit) : PLift (Nonempty GoalProp) :=
    safe_goal_nonempty u

  noncomputable def my_inst (n : ℕ) (hn : n > 0) : Inhabited GoalProp :=
    ⟨(Classical.choice (safe_goal_nonempty ()).down) n hn⟩
end
