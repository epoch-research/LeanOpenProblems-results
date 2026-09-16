import Mathlib

lemma decide_le_sub_of_add_le {a b c : ℕ} (h : a ≤ c) :
  decide (a + b ≤ c) = true ↔ decide (b ≤ c - a) = true := by
  simp only [decide_eq_true_eq]
  omega

lemma decide_le_sub_of_add_gt {a b c : ℕ} (h : a > c) :
  ¬(decide (a + b ≤ c) = true) := by
  simp only [decide_eq_true_eq, not_le]
  omega
