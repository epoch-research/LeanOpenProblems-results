import Mathlib

theorem test_algebraic (q' d' d : ℝ) (k : ℕ) :
    (10 * q' + d' : ℝ) + d / (10 : ℝ)^k = 10 * (q' + ((10 : ℝ)^k * d' + d) / (10 : ℝ)^(k + 1)) := by
  have h_pow : (10 : ℝ)^(k+1) = (10 : ℝ)^k * 10 := pow_succ 10 k
  rw [h_pow]
  have h_ne : (10 : ℝ)^k ≠ 0 := by positivity
  field_simp
  ring
