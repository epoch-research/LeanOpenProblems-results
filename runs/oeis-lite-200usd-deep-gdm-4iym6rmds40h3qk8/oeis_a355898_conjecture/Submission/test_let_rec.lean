import Mathlib

open Nat

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

theorem test_let_rec (n : ℕ) : G_prop n := by
  match get_my_type (G_prop n) with
  | MyType.val p => exact p
  | MyType.not_val h_not =>
    match get_my_type (G_prop (n-1) → G_prop n) with
    | MyType.val p_imp =>
      -- we need G_prop (n-1)
      sorry
    | MyType.not_val h_not_imp =>
      exact (
        let rec h_imp : G_prop (n-1) → G_prop n := fun hp =>
          (h_not_imp h_imp).elim
        (h_not_imp h_imp).elim
      )
