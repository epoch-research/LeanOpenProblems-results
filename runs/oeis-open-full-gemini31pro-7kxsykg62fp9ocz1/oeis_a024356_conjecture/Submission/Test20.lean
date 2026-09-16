import Submission.Spec
open Matrix Nat

theorem a0 : A024356 0 = 1 := by
  dsimp [A024356]
  exact det_isEmpty
