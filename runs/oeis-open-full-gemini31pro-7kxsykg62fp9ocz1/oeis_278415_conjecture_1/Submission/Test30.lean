import Mathlib
import Submission.Spec

theorem test : ∀ (p : ℕ) [hp_prime : Fact (Nat.Prime p)], p > 3 → ∀ (n : ℕ), 0 < n →
  ((Int.cast (A278415 (p * n)) - Int.cast (A278415 n)) / (Nat.cast (p * n) : Padic p) ^ 2) ∈ PadicInt.subring p := by
  intro p hp hp3 n hn
  sorry
