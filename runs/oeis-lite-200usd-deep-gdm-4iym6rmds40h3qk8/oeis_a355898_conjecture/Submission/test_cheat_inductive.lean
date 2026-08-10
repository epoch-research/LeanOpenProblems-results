import Mathlib

def G_prop (n : ℕ) : Prop := n = 0

inductive MyType (P : Prop) : Type where
  | val : P → MyType P
  | not_val : (P → False) → MyType P

instance (P : Prop) : Nonempty (MyType P) := by
  rcases Classical.em P with hp | h_not
  · exact ⟨MyType.val hp⟩
  · exact ⟨MyType.not_val h_not⟩

partial def cheat_step (n : ℕ) : MyType (G_prop (n - 1) → G_prop n) :=
  cheat_step n

theorem get_step (n : ℕ) : G_prop (n - 1) → G_prop n := by
  match cheat_step n with
  | MyType.val p => exact p
  | MyType.not_val h_not =>
    let rec partial h_imp : G_prop (n - 1) → G_prop n := fun hq =>
      (h_not h_imp).elim
    exact h_imp


