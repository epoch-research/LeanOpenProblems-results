import FormalConjectures.Util.ProblemImports
open Nat BigOperators Finset

example (t : ℕ) : (((Int.ofNat t) * (3 * (Int.ofNat t) + 2)).toNat) = t * (3*t+2) := by
  apply Nat.cast_injective (R := ℤ)
  rw [Int.toNat_of_nonneg]
  · norm_num
  · show (0 : ℤ) ≤ (t : ℤ) * (3 * (t : ℤ) + 2)
    nlinarith [show (0 : ℤ) ≤ t by exact_mod_cast Nat.zero_le t]

example (t : ℕ) : (((Int.negSucc t) * (3 * (Int.negSucc t) + 2)).toNat) = (t+1) * (3*(t+1)-2) := by
  apply Nat.cast_injective (R := ℤ)
  rw [Int.toNat_of_nonneg]
  · have h2 : 2 ≤ 3 * (t + 1) := by nlinarith
    rw [Int.negSucc_eq]
    norm_num [Nat.cast_sub h2]
    ring
  · rw [Int.negSucc_eq]
    show (0 : ℤ) ≤ (-(↑t + 1)) * (3 * (-(↑t + 1)) + 2)
    nlinarith [show (0 : ℤ) ≤ t by exact_mod_cast Nat.zero_le t]
