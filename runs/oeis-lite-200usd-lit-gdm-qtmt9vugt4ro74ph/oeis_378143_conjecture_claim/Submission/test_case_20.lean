import FormalConjectures.Util.ProblemImports

set_option exponentiation.threshold 2000000
set_option maxRecDepth 2000000

open Nat

theorem test_20 (h : Nat.Prime (10 ^ (2 ^ 20) + 1)) : False := by
  have hdvd : 167772161 ∣ 10 ^ (2 ^ 20) + 1 := by
    rw [← ZMod.natCast_eq_zero_iff]
    have : (10 : ZMod 167772161) ^ (2 ^ 20) + 1 = 0 := by
      reduce_mod_char
    exact_mod_cast this
  have h_lt : 167772161 < 10 ^ (2 ^ 20) + 1 := by
    have h1 : 167772161 < 10 ^ 9 + 1 := by decide
    apply lt_of_lt_of_le h1
    apply Nat.add_le_add_right
    apply Nat.pow_le_pow_right (by decide)
    show 9 ≤ 2 ^ 20
    decide
  apply Nat.not_prime_of_dvd_of_ne (m := 167772161) at h
  · exact h
  · exact hdvd
  · decide
  · exact Nat.ne_of_lt h_lt
