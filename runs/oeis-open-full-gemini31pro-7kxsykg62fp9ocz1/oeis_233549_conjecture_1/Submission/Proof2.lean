import Mathlib

open Nat

lemma x_le_x4_add_1 (x : ℕ) : x ≤ x ^ 4 + 1 := by
  rcases Nat.eq_zero_or_pos x with rfl | hx
  · simp
  · calc x = x ^ 1 := (pow_one x).symm
      _ ≤ x ^ 4 := Nat.pow_le_pow_right hx (by decide)
      _ ≤ x ^ 4 + 1 := by omega

lemma bdd_of_finite (S : Set ℕ) (h : S.Finite) : ∃ B, ∀ y ∈ S, y ≤ B := by
  exact h.bddAbove
