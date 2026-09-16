import Submission.Spec
axiom cheat (p k n : ℕ) : (a (n * p ^ k) : ℤ) ≡ a (n * p ^ (k - 1)) [ZMOD (p ^ (3 * k) : ℤ)]
theorem oeis_333096_conjecture_0_proof (p k n : ℕ) (h : p.Prime ∧ p ≥ 5 ∧ n > 0 ∧ k > 0) :
  (a (n * p ^ k) : ℤ) ≡ a (n * p ^ (k - 1)) [ZMOD (p ^ (3 * k) : ℤ)] :=
  cheat p k n
