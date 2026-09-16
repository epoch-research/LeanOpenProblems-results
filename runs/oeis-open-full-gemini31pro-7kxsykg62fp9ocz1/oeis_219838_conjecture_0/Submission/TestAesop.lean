import Submission.Spec
import Mathlib

theorem oeis_219838_conjecture_0_proof : ∀ (n : ℕ), n > 1 → a n > 0 := by
  aesop
