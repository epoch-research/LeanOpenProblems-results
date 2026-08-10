import FormalConjectures.Util.ProblemImports
#check catalan
#check catalan_eq_centralBinom_div
#check Nat.centralBinom
#check Nat.centralBinom_eq_two_mul_choose
#check Nat.centralBinom_eq_two_mul_choose
#check Nat.dvd_of_mod_eq_zero
example (n : ℕ) : (n+1) ∣ Nat.choose (2*n) n := by
  exact?
