import Mathlib

lemma prime_exists (n : ℕ) (hn : 1 ≤ n) : ∃ p, Nat.Prime p ∧ n < p ∧ p ≤ 2 * n := by
  apply Nat.exists_prime_lt_and_le_two_mul
  omega
