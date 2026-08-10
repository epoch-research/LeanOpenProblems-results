import FormalConjectures.Util.ProblemImports

set_option exponentiation.threshold 100000
set_option maxRecDepth 100000

open Nat Set

theorem test_17 (h : (10 ^ (2 ^ 17) + 1).Prime) : False := by
  have hdvd : 175636481 ∣ 10 ^ (2 ^ 17) + 1 := by
    rw [← ZMod.natCast_eq_zero_iff]
    have : (10 : ZMod 175636481) ^ (2 ^ 17) + 1 = 0 := by
      reduce_mod_char
    exact_mod_cast this
  apply Nat.not_prime_of_dvd_of_ne (m := 175636481) at h
  · exact h
  · exact hdvd
  · decide
  · decide

theorem test_18 (h : (10 ^ (2 ^ 18) + 1).Prime) : False := by
  have hdvd : 639631361 ∣ 10 ^ (2 ^ 18) + 1 := by
    rw [← ZMod.natCast_eq_zero_iff]
    have : (10 : ZMod 639631361) ^ (2 ^ 18) + 1 = 0 := by
      reduce_mod_char
    exact_mod_cast this
  apply Nat.not_prime_of_dvd_of_ne (m := 639631361) at h
  · exact h
  · exact hdvd
  · decide
  · decide

theorem test_19 (h : (10 ^ (2 ^ 19) + 1).Prime) : False := by
  have hdvd : 70254593 ∣ 10 ^ (2 ^ 19) + 1 := by
    rw [← ZMod.natCast_eq_zero_iff]
    have : (10 : ZMod 70254593) ^ (2 ^ 19) + 1 = 0 := by
      reduce_mod_char
    exact_mod_cast this
  apply Nat.not_prime_of_dvd_of_ne (m := 70254593) at h
  · exact h
  · exact hdvd
  · decide
  · decide

theorem test_20 (h : (10 ^ (2 ^ 20) + 1).Prime) : False := by
  have hdvd : 167772161 ∣ 10 ^ (2 ^ 20) + 1 := by
    rw [← ZMod.natCast_eq_zero_iff]
    have : (10 : ZMod 167772161) ^ (2 ^ 20) + 1 = 0 := by
      reduce_mod_char
    exact_mod_cast this
  apply Nat.not_prime_of_dvd_of_ne (m := 167772161) at h
  · exact h
  · exact hdvd
  · decide
  · decide
