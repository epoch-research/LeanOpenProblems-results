import Mathlib

inductive MyType (P : Prop) : Type where
  | val : P → MyType P
  | not_val : (P → False) → MyType P

instance (P : Prop) : Nonempty (MyType P) := by
  rcases Classical.em P with hp | h_not
  · exact ⟨MyType.val hp⟩
  · exact ⟨MyType.not_val h_not⟩

attribute [local instance] Classical.inhabited_of_nonempty

partial def get_my_type_partial (P : Prop) : MyType P :=
  get_my_type_partial P

partial def solve_negation_partial (P : Prop) (h_not : ¬ P) : MyType False :=
  match get_my_type_partial (¬ P) with
  | MyType.val h_not2 =>
    solve_negation_partial P h_not2
  | MyType.not_val h_not_not =>
    MyType.val (h_not_not h_not)

theorem get_false (P : Prop) (h_not : ¬ P) : False := by
  match solve_negation_partial P h_not with
  | MyType.val f => exact f
  -- wait, is there a second branch?
  -- MyType.not_val hn
  -- Let's see if we can resolve the second branch.
