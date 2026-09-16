import Submission.Spec
open Nat Finset

theorem proof : ∀ (n : ℕ), 0 < n → ¬ (a n = 0 ∧ b n < 0) := by
  exact?
