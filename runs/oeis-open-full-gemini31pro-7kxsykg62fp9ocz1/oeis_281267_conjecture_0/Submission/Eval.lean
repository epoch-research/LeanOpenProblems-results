import Submission.Spec
import Mathlib

theorem oeis_281267_conjecture_0_test (p : ℕ) (n k : ℕ) :
  Nat.Prime p → 3 ≤ p → 1 ≤ n → 1 ≤ k →
  a (n * p ^ k) ≡ a (n * p ^ (k - 1)) [ZMOD ((p ^ (2 * k) : ℕ) : ℤ)] := by
  intros
  exact?
