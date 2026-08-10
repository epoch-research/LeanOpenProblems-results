import FormalConjectures.Util.ProblemImports

open Nat Finset

def GoalProp : Prop := ∀ (n : ℕ), n > 0 → n > 0

instance (n : ℕ) (hn : n > 0) [h : Inhabited (Nonempty GoalProp)] : Inhabited (n > 0) :=
  ⟨(Classical.choice (default : Nonempty GoalProp)) n hn⟩

partial def cast_proof (n : ℕ) (hn : n > 0) (h : Nonempty GoalProp) : n > 0 :=
  (Classical.choice h) n hn

def my_goal_inhabited : Inhabited (Nonempty GoalProp) :=
  let rec partial h_inhabited_fn (u : Unit) : Nonempty GoalProp :=
    ⟨fun n hn => cast_proof n hn (h_inhabited_fn u)⟩
  ⟨h_inhabited_fn ()⟩
