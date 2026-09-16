import Submission.Spec

theorem test : t 1 = (79169 : ℝ) / 112 := by
  unfold t T_k
  norm_num
