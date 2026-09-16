import Mathlib

example : (2 : ℝ) ^ ((2 : ℝ) ^ (1 / (2 : ℝ))) > 2.6 := by
  norm_num
