import FormalConjectures.Util.ProblemImports
open Rat Nat

def continued_fraction_denominator (n k : ℕ) : ℚ :=
  if n ≤ 2 then 0
  else
    if 2 ≤ k ∧ k ≤ n - 1 then
      if k = n - 1 then
        (k : ℚ) + (n : ℚ) / 4
      else
        let R_next := continued_fraction_denominator n (k + 1)
        (k : ℚ) - (k + 1 : ℚ) / R_next
    else 0
termination_by n - k
#print continued_fraction_denominator.induct
#print continued_fraction_denominator.eq_def
#check Rat.num_divInt
#check Rat.den_divInt
#check Rat.num_den_mk
#check Rat.reduced
#check Rat.num_coprime_den
#check Rat.num_ne_zero
#check Rat.divInt_eq_div
#check Rat.mkRat
#check Rat.mkRat_self
#check Nat.dvd_factorial
#check Nat.Prime.coprime_iff_not_dvd
#check ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_one
