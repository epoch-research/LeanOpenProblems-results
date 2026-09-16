import Mathlib

theorem foo (k : ℕ) (h1 : 0 < k) (h2 : (k : ℝ) < 3 * Real.sqrt (38 : ℝ) + 3) : k ≤ 21 := by
  by_contra! h
  have hk : (22 : ℝ) ≤ k := by exact_mod_cast h
  have h3 : (19 : ℝ) ≤ k - 3 := by linarith
  have h4 : (361 : ℝ) ≤ (k - 3)^2 := by
    calc (361 : ℝ) = 19 * 19 := by norm_num
      _ ≤ (k - 3) * (k - 3) := mul_self_le_mul_self (by norm_num) h3
      _ = (k - 3)^2 := by ring
  have h5 : (k - 3 : ℝ) < 3 * Real.sqrt 38 := by linarith
  have hr : (0 : ℝ) ≤ 3 * Real.sqrt 38 := by positivity
  have h6 : (k - 3 : ℝ)^2 < 342 := by
    calc (k - 3 : ℝ)^2 = (k - 3) * (k - 3) := by ring
      _ < (3 * Real.sqrt 38) * (3 * Real.sqrt 38) := by
        nlinarith [h5, show 0 ≤ (k - 3 : ℝ) by linarith, hr]
      _ = 9 * 38 := by
        calc (3 * Real.sqrt 38) * (3 * Real.sqrt 38) = 9 * (Real.sqrt 38)^2 := by ring
          _ = 9 * 38 := by rw [Real.sq_sqrt (by norm_num)]
      _ = 342 := by norm_num
  linarith
