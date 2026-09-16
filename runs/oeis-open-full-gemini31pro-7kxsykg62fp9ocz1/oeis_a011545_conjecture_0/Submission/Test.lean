import Mathlib

open Real Int

theorem oeis_a011545_conjecture_0_is_true : 
  (∀ n : ℕ, ¬ ∃ (k : ℤ),
      (Real.pi * (10 : ℝ) ^ n.cast < k.cast) ∧
      (k.cast < Real.pi / Real.arctan (1 / (10 : ℝ) ^ n.cast))) := by
  sorry
