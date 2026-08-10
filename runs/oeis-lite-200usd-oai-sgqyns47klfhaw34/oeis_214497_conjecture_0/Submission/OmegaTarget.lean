import FormalConjectures.Util.ProblemImports
open Nat

example (n k : ℕ) (hk : 3 ^ n ≤ k) :
    ¬ (Nat.Prime ((3 ^ n - k) * (2 ^ n) - 1) ∧ Nat.Prime ((3 ^ n - k) * (2 ^ n) + 1)) := by
  intro h
  have hsub : 3 ^ n - k = 0 := Nat.sub_eq_zero_of_le hk
  have hzero : (3 ^ n - k) * (2 ^ n) - 1 = 0 := by simp [hsub]
  exact Nat.not_prime_zero (by simpa [hzero] using h.1)
