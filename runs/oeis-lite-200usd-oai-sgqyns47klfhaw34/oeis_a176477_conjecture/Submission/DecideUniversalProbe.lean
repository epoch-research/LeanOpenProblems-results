import Submission.Spec
example : (∀ (n : ℕ), n ≥ 1 → a n > 0 ∧ (Odd (a n) ↔ ∃ m : ℕ, m ≥ 1 ∧ n = 2^m)) := by
  native_decide
