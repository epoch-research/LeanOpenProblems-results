import Mathlib

theorem foo (k : ℕ) (h1 : 0 < k) (h2 : (k : ℝ) < 3 * Real.sqrt (38 : ℝ) + 3) : k ≤ 21 := by
  have : (k - 3 : ℝ) < 3 * Real.sqrt 38 := by linarith
  have h3 : (k - 3 : ℝ)^2 < (3 * Real.sqrt 38)^2 := sorry
  sorry
