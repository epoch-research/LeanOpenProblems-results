import FormalConjectures.Util.ProblemImports

set_option exponentiation.threshold 2000000
set_option maxRecDepth 2000000

theorem not_prime_10_2_22 : ¬ Nat.Prime (10 ^ (2 ^ 22) + 1) := by
  have h_div : 101702694862849 ∣ 10 ^ (2 ^ 22) + 1 := Nat.dvd_of_mod_eq_zero (by decide)
  sorry
