import Submission.Spec
open Nat

#check ¬ (∀ (p k n : ℕ),
  (p.Prime ∧ p ≥ 5 ∧ n > 0 ∧ k > 0) →
  (a (n * p ^ k) : ℤ) ≡ a (n * p ^ (k - 1)) [ZMOD (p ^ (3 * k) : ℤ)])
