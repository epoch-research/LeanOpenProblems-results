import Mathlib

lemma sqrt_log_gt_two {x : ℝ} (hx : 4 < x) : 2 < x ^ (1/2 : ℝ) := by
  calc
    (2 : ℝ) = 4 ^ (1/2 : ℝ) := by norm_num
    _ < x ^ (1/2 : ℝ) := by
      apply Real.rpow_lt_rpow (by norm_num) hx (by norm_num)
