import FormalConjectures.Util.ProblemImports
open Nat Set

example (n : ℕ) : ∃ k : ℕ, Nat.xor (k ^ 2) ((k + 1) ^ 2) = (2 * n + 1) ^ 2 := by
  aesop

#check Nat.testBit_xor
#check Nat.testBit_two_pow
#check Nat.ext
#check Nat.eq_of_testBit_eq
#check Nat.bit
#check Nat.bit_eq
#check Nat.xor_bit
#check Nat.bits_inj
