import FormalConjectures.Util.ProblemImports

set_option exponentiation.threshold 150000
set_option maxRecDepth 150000

open Nat Set

abbrev exp17 : ℕ := 131072

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
