import Mathlib

lemma limit_bounds (E : ℝ) (hE1 : 16/9 < E) (hE2 : E < 41/23) :
    35/10 < (E - 1) / (2 - E) ∧ (E - 1) / (2 - E) < 36/10 := by
  have : 2 - E > 0 := by linarith
  constructor
  · rw [lt_div_iff₀ this]
    linarith
  · rw [div_lt_iff₀ this]
    linarith
