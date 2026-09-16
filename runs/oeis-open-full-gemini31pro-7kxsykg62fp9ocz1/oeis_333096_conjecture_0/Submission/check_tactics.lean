import Submission.Spec
open Nat

theorem test (p k n : ℕ) (h : p.Prime ∧ p ≥ 5 ∧ n > 0 ∧ k > 0) :
  (a (n * p ^ k) : ℤ) ≡ a (n * p ^ (k - 1)) [ZMOD (p ^ (3 * k) : ℤ)] := by
  unfold a
  sorry
