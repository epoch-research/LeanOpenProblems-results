import Submission.Spec
open Real

lemma check_expr : ((3 / 2) ^ (3 : ℝ) : ℝ) = 1 := by
  norm_num

lemma check_expr2 : ((3 / 2) ^ (3 : ℝ) : ℝ) = 3.375 := by
  norm_num
