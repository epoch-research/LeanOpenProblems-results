import Mathlib

theorem foo (k : ℕ) (h1 : 0 < k) (h2 : (k : ℝ) < 3 * Real.sqrt (38 : ℝ) + 3) : k ≤ 21 := by
  by_contra! h
  have hk : (22 : ℝ) ≤ k := by exact_mod_cast h
  have h3 : (19 : ℝ) ≤ k - 3 := by linarith
  have h4 : (19 : ℝ)^2 ≤ (k - 3)^2 := by nlinarith
  have h5 : (k - 3 : ℝ) < 3 * Real.sqrt 38 := by linarith
  have hr : (0 : ℝ) ≤ 3 * Real.sqrt 38 := by positivity
  have h6 : (k - 3 : ℝ)^2 < (3 * Real.sqrt 38)^2 := by
    nlinarith [show 0 ≤ k - 3 by linarith, hr, h5]
  have h7 : (3 * Real.sqrt 38 : ℝ)^2 = 9 * 38 := by
    calc (3 * Real.sqrt 38 : ℝ)^2 = 3^2 * (Real.sqrt 38)^2 := by ring
      _ = 9 * 38 := by
        rw [Real.sq_sqrt (by norm_num)]
        norm_num
  linarith
