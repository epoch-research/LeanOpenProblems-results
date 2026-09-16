import Submission.Spec
import Mathlib.Tactic.NormNum.Prime
open OeisA230507

theorem test_9 : ∃ (x y z : ℕ), 9 = x + y + z ∧ P2_condition x ∧ P2_condition y ∧ Z_condition z := by
  use 2, 5, 2
  unfold P2_condition Z_condition
  norm_num
