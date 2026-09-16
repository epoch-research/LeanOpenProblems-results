import Submission.Spec

theorem test : t 0 = 367 := by
  unfold t T_k
  norm_num
