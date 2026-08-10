import FormalConjectures.Util.ProblemImports

set_option exponentiation.threshold 150000
set_option maxRecDepth 150000

open Nat Set

abbrev exp16 : ℕ := 65536
abbrev exp17 : ℕ := 131072
abbrev exp18 : ℕ := 262144
abbrev exp19 : ℕ := 524288
abbrev exp20 : ℕ := 1048576

theorem test_16 (h : (10 ^ exp16 + 1).Prime) : False := by
  have hdvd : 8257537 ∣ 10 ^ exp16 + 1 := by
    rw [← ZMod.natCast_eq_zero_iff]
    have : (10 : ZMod 8257537) ^ exp16 + 1 = 0 := by
      reduce_mod_char
    exact_mod_cast this
  apply Nat.not_prime_of_dvd_of_ne (m := 8257537) at h
  · exact h
  · exact hdvd
  · decide
  · decide

theorem test_17 (h : (10 ^ exp17 + 1).Prime) : False := by
  have hdvd : 175636481 ∣ 10 ^ exp17 + 1 := by
    rw [← ZMod.natCast_eq_zero_iff]
    have : (10 : ZMod 175636481) ^ exp17 + 1 = 0 := by
      reduce_mod_char
    exact_mod_cast this
  apply Nat.not_prime_of_dvd_of_ne (m := 175636481) at h
  · exact h
  · exact hdvd
  · decide
  · decide

theorem test_18 (h : (10 ^ exp18 + 1).Prime) : False := by
  have hdvd : 639631361 ∣ 10 ^ exp18 + 1 := by
    rw [← ZMod.natCast_eq_zero_iff]
    have : (10 : ZMod 639631361) ^ exp18 + 1 = 0 := by
      reduce_mod_char
    exact_mod_cast this
  apply Nat.not_prime_of_dvd_of_ne (m := 639631361) at h
  · exact h
  · exact hdvd
  · decide
  · decide

theorem test_19 (h : (10 ^ exp19 + 1).Prime) : False := by
  have hdvd : 70254593 ∣ 10 ^ exp19 + 1 := by
    rw [← ZMod.natCast_eq_zero_iff]
    have : (10 : ZMod 70254593) ^ exp19 + 1 = 0 := by
      reduce_mod_char
    exact_mod_cast this
  apply Nat.not_prime_of_dvd_of_ne (m := 70254593) at h
  · exact h
  · exact hdvd
  · decide
  · decide

theorem test_20 (h : (10 ^ exp20 + 1).Prime) : False := by
  have hdvd : 167772161 ∣ 10 ^ exp20 + 1 := by
    rw [← ZMod.natCast_eq_zero_iff]
    have : (10 : ZMod 167772161) ^ exp20 + 1 = 0 := by
      reduce_mod_char
    exact_mod_cast this
  apply Nat.not_prime_of_dvd_of_ne (m := 167772161) at h
  · exact h
  · exact hdvd
  · decide
  · decide
