import Submission.Spec
open OeisA230507

theorem test : ∀ n : ℕ, n > 8 → ∃ (x y z : ℕ), n = x + y + z ∧ P2_condition x ∧ P2_condition y ∧ Z_condition z :=
  answer(sorry)
