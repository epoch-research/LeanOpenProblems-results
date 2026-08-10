import Mathlib

inductive MyType (P : Prop) : Type where
  | val : P → MyType P
  | not_val : (P → False) → MyType P

instance (P : Prop) : Nonempty (MyType P) := by
  rcases Classical.em P with hp | h_not
  · exact ⟨MyType.val hp⟩
  · exact ⟨MyType.not_val h_not⟩

partial def get_my_type (P : Prop) : MyType P := get_my_type P

theorem prove_it (P : Prop) : P := by
  match get_my_type P with
  | MyType.val p => exact p
  | MyType.not_val h_not =>
    -- wait, can we do get_my_type again?
    sorry
