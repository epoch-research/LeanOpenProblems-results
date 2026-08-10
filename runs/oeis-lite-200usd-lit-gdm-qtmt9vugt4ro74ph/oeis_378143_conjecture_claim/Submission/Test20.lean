import FormalConjectures.Util.ProblemImports

set_option exponentiation.threshold 100000
set_option maxRecDepth 100000

open Nat Set

abbrev exp18 : ℕ := 262144

theorem test_18 (h : (10 ^ exp18 + 1).Prime) : False := by
  have hdvd : 639631361 ∣ 10 ^ exp18 + 1 := by
    rw [← ZMod.natCast_eq_zero_iff]
    have : (10 : ZMod 639631361) ^ exp18 + 1 = 0 := by
      reduce_mod_char
    exact_mod_cast this
  have h_le : 10 ^ 9 ≤ 10 ^ exp18 := Nat.pow_le_pow_right (by decide) (by decide)
  have h_lt : 639631361 < 10 ^ exp18 + 1 := by
    omega
  apply Nat.not_prime_of_dvd_of_ne (m := 639631361) at h
  · exact h
  · exact hdvd
  · decide
  · exact ne_of_lt h_lt
