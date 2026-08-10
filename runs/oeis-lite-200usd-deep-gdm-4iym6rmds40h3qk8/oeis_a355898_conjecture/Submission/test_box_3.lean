import Mathlib

inductive MyType (P : Prop) : Type where
  | val : P → MyType P
  | not_val : (P → False) → MyType P

instance (P : Prop) : Nonempty (MyType P) := by
  rcases Classical.em P with hp | h_not
  · exact ⟨MyType.val hp⟩
  · exact ⟨MyType.not_val h_not⟩

partial def get_my_type (P : Prop) : MyType P :=
  get_my_type P

theorem prove_any (P : Prop) : P := by
  rcases get_my_type P with ⟨hp⟩ | ⟨h_not⟩
  · exact hp
  · -- wait, how to get a proof of P from h_not?
    sorry
