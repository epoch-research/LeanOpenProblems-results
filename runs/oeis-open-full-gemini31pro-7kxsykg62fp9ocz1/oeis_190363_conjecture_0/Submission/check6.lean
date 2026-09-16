import Mathlib

example : (156 : ℝ) ≤ Real.sqrt 24500 := by
  rw [Real.le_sqrt (by norm_num) (by norm_num)]
  norm_num

example : Real.sqrt 24500 < (157 : ℝ) := by
  rw [Real.sqrt_lt (by norm_num) (by norm_num)]
  norm_num
