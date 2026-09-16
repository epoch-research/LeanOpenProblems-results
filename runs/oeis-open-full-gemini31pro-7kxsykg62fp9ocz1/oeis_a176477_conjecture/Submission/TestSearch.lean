import Submission.Spec

theorem test : ∀ (n : ℕ) (hn : n ≥ 1), a n > 0 ∧ (Odd (a n) ↔ ∃ m : ℕ, m ≥ 1 ∧ n = 2^m) := by
  exact?
