import Submission.Spec
import Aesop

theorem test : ∀ (n : ℕ), 0 < n → ¬ (a n = 0 ∧ b n < 0) := by
  aesop
