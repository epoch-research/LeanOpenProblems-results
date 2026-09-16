import Mathlib

example : (2 : ℝ) ^ ((2 : ℝ) ^ (1 / (2 : ℝ))) < 2.67 := by
  norm_num
