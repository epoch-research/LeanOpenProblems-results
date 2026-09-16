import Submission.Spec
open Real

theorem waring_g_4 : waring_g 4 = 19 := by
  dsimp [waring_g]
  norm_num
