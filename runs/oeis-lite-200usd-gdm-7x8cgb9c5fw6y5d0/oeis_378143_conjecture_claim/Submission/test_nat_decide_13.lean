import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Nat.Basic

theorem not_prime_of_fermat_witness_nat (N a : ℕ) (h_prime : Nat.Prime N) (ha : a < N) (ha1 : 1 < a)
    (h_witness : a ^ (N - 1) % N ≠ 1) : False := by
  sorry
