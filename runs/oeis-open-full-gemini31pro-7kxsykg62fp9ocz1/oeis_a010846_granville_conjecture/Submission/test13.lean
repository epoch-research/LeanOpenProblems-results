import Mathlib

lemma test_linarith (a : ℕ) (p : ℝ) (H2 : p ≤ a) (h_a : a ≤ 2) (h_p : 2 < p) : False := by
  have h_a_R : (a : ℝ) ≤ 2 := Nat.cast_le.mpr h_a
  linarith
