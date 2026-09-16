import Mathlib

example : Int.floor ((140 : ℝ) * Real.sqrt (5/4)) = 156 := by
  apply Int.floor_eq_iff.mpr
  constructor
  · have h1 : (140 : ℝ) = Real.sqrt 19600 := by
      rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 140)]
      congr
      norm_num
    rw [h1, ← Real.sqrt_mul (by norm_num)]
    have h2 : (19600 : ℝ) * (5/4) = 24500 := by norm_num
    rw [h2]
    rw [Real.le_sqrt (by norm_num) (by norm_num)]
    norm_num
  · push_cast
    have h1 : (140 : ℝ) = Real.sqrt 19600 := by
      rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 140)]
      congr
      norm_num
    rw [h1, ← Real.sqrt_mul (by norm_num)]
    have h2 : (19600 : ℝ) * (5/4) = 24500 := by norm_num
    rw [h2]
    rw [Real.sqrt_lt (by norm_num) (by norm_num)]
    norm_num
