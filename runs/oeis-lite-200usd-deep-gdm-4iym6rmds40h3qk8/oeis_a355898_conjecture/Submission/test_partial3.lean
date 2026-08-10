import Mathlib

def G_prop (n : ℕ) : Prop := n = n

inductive MyType (P : Prop) : Type where
  | val : P → MyType P
  | not_val : (P → False) → MyType P

instance (P : Prop) : Nonempty (MyType P) := by
  rcases Classical.em P with hp | h_not
  · exact ⟨MyType.val hp⟩
  · exact ⟨MyType.not_val h_not⟩

partial def get_my_type (P : Prop) : MyType P :=
  get_my_type P

partial def get_G_prop_val (n : ℕ) : G_prop n :=
  match get_my_type (G_prop n) with
  | MyType.val p => p
  | MyType.not_val h => (h (get_G_prop_val n)).elim
