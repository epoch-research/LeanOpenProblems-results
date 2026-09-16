import Mathlib

example : 1 / (2 : ℝ) = 0.5 := by
  norm_num

example : (2 : ℝ) ^ ((2 : ℝ) ^ (1 / (2 : ℝ))) > 2.5 := by
  sorry
