import Submission.Spec
open Nat

theorem oeis_333096_conjecture_0_proof (p k n : ℕ) :
  (p.Prime ∧ p ≥ 5 ∧ n > 0 ∧ k > 0) →
  (a (n * p ^ k) : ℤ) ≡ a (n * p ^ (k - 1)) [ZMOD (p ^ (3 * k) : ℤ)] := by
  exact?
