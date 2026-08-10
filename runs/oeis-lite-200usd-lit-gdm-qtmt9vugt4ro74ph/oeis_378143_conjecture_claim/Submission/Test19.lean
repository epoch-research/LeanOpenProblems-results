import FormalConjectures.Util.ProblemImports

set_option exponentiation.threshold 150000
set_option maxRecDepth 150000

open Nat Set

abbrev exp18 : ℕ := 262144

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
