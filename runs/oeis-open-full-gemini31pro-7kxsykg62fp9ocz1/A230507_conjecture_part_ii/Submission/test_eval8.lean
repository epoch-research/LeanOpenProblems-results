import Submission.Spec
open OeisA230507

theorem n9 : ∃ (x y z : ℕ), 9 = x + y + z ∧ P2_condition x ∧ P2_condition y ∧ Z_condition z :=
  ⟨2, 5, 2, rfl, by decide, by decide, by decide⟩
