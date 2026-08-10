import Mathlib

inductive MyType (P : Prop) : Type where
  | val : P → MyType P
  | not_val : (P → False) → MyType P

instance (P : Prop) : Nonempty (MyType P) := by
  rcases Classical.em P with hp | h_not
  · exact ⟨MyType.val hp⟩
  · exact ⟨MyType.not_val h_not⟩

partial def get_my_type_partial (P : Prop) : MyType P :=
  get_my_type_partial P

def solve_negation_non_partial : (P : Prop) → (h_not : ¬ P) → (k : ℕ) → Empty
  | P, h_not, 0 =>
    let rec partial f (u : Unit) : Empty := f u
    f ()
  | P, h_not, k' + 1 =>
    match get_my_type_partial (¬ P) with
    | MyType.val h_not2 =>
      solve_negation_non_partial P h_not2 k'
    | MyType.not_val h_not_not =>
      (h_not_not h_not).elim
termination_by P h_not k => k
decreasing_by
  simp_wf
  omega
