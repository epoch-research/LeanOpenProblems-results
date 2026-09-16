import Submission.Spec
open Nat

lemma t_1_eq : t 1 = 79169 / 112 := by
  unfold t T_k
  norm_num
