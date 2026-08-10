import Submission.Spec

theorem verify : ∀ (p : ℕ) (hp : Nat.Prime p) (hp5 : 5 ≤ p) (n : ℕ),
  (2 * p + 3) / 3 ≤ n → n ≤ p - 1 → (p ^ 3 : ℕ) ∣ a n :=
  oeis_374605_conjecture_0
