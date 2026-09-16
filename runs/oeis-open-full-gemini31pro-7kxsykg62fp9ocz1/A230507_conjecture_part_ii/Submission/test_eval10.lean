import Submission.Spec
open OeisA230507

theorem n9 : ∃ (x y z : ℕ), 9 = x + y + z ∧ P2_condition x ∧ P2_condition y ∧ Z_condition z := by
  use 2, 5, 2
  dsimp [P2_condition, Z_condition]
  norm_num
