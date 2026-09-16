import Mathlib

example : (140 : ℝ) * Real.sqrt (5/4) = Real.sqrt 24500 := by
  have h1 : (140 : ℝ) = Real.sqrt 19600 := by
    rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 140)]
    congr
    norm_num
  rw [h1, ← Real.sqrt_mul (by norm_num)]
  congr
  norm_num

