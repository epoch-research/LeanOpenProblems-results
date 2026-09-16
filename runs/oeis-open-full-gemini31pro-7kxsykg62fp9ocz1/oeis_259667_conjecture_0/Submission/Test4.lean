import Submission.Spec
import Mathlib

theorem check_conj :
    (∀ k : ℕ, A259667 (2^k - 1) = 1 ↔ k = 0 ∨ k = 1 ∨ k = 5) ∧
    (∀ k : ℕ, A259667 (2^k - 1) = 5 ↔ k = 2 ∨ k = 8) ∧
    (∀ k : ℕ, k > 8 → A259667 (2^k - 1) = 3) := by
  exact?
