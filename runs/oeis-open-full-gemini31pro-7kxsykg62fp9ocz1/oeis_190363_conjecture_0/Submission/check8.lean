import Mathlib

lemma floor_val (n : ℕ) (n_sqr : ℕ) (val : ℕ) (flr : ℤ)
    (h_n_sqr : (n : ℝ)^2 = (n_sqr : ℝ))
    (h_val : (n_sqr : ℝ) * (5/4) = (val : ℝ))
    (h_le : (flr : ℝ)^2 ≤ (val : ℝ))
    (h_lt : (val : ℝ) < ((flr + 1 : ℤ) : ℝ)^2) :
    Int.floor ((n : ℝ) * Real.sqrt (5/4)) = flr := by
  apply Int.floor_eq_iff.mpr
  constructor
  · have h1 : (n : ℝ) = Real.sqrt (n_sqr : ℝ) := by
      rw [← Real.sqrt_sq (by positivity), h_n_sqr]
    rw [h1, ← Real.sqrt_mul (by positivity), h_val]
    rw [Real.le_sqrt (by positivity) (by positivity)]
    exact h_le
  · push_cast
    have h1 : (n : ℝ) = Real.sqrt (n_sqr : ℝ) := by
      rw [← Real.sqrt_sq (by positivity), h_n_sqr]
    rw [h1, ← Real.sqrt_mul (by positivity), h_val]
    rw [Real.sqrt_lt (by positivity) (by positivity)]
    exact h_lt
