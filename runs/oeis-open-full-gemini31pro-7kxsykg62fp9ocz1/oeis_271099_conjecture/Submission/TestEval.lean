import Submission.Spec
open Real Int

lemma test_waring_3 : waring_g 3 = 9 := by
  dsimp [waring_g]
  norm_num
