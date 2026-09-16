import Submission.Spec
open Real Int

lemma waring_g_3_eq_9 : waring_g 3 = 9 := by
  dsimp [waring_g]
  norm_num
