import Submission.Spec

theorem disproof : ¬ (A024356 4 = 0 ∧ ∀ n : ℕ, A024356 n = 0 → n = 4) := by
  aesop
