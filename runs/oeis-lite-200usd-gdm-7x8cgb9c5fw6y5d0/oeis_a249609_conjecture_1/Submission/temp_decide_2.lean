import FormalConjectures.Util.ProblemImports

open Nat List

example : (9 : ℕ).bits = [true, false, false, true] := by
  have h_9 : (9 : ℕ) = 2 * 4 + 1 := by norm_num
  rw [h_9, Nat.bit1_bits]
  have h_4 : (4 : ℕ) = 2 * 2 := by norm_num
  erw [h_4, Nat.bit0_bits 2 (by decide)]
  have h_2 : (2 : ℕ) = 2 * 1 := by norm_num
  erw [h_2, Nat.bit0_bits 1 (by decide)]
  rw [Nat.one_bits]
