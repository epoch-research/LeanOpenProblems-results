import Submission.Spec
import Mathlib

theorem oeis_379643_conjecture_0_proof : ∀ (n : ℕ), 0 < n → ¬ (a n = 0 ∧ b n < 0) := by
  aesop
