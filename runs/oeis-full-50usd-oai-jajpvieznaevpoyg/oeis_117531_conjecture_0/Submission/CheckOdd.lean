import FormalConjectures.Util.ProblemImports
#check Nat.coprime_two_right
#check Nat.Coprime.pow_right
#check Nat.Coprime.pow_left
#check Nat.Coprime.dvd_of_dvd_mul_right
#check Nat.dvd_of_mod_eq_zero
#check Nat.mod_eq_of_lt
example {q : ℕ} (h : q % 2 = 1) : (q + 1) / 2 * 2 = q + 1 := by omega
