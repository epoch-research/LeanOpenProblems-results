import FormalConjectures.Util.ProblemImports
set_option exponentiation.threshold 10000
set_option maxHeartbeats 20000000
set_option maxRecDepth 1000000
example : 3 ∣ ((1 + 1) ^ (Nat.totient (1408 - 1) / 2) - 1 : ℕ) := by
  have ht : Nat.totient (1408 - 1) / 2 = 396 := by decide
  rw [ht]
  norm_num [Nat.dvd_iff_mod_eq_zero, Nat.pow_mod]
example : 3 < ((1 + 1) ^ (Nat.totient (1408 - 1) / 2) - 1 : ℕ) := by
  have ht : Nat.totient (1408 - 1) / 2 = 396 := by decide
  rw [ht]
  norm_num
