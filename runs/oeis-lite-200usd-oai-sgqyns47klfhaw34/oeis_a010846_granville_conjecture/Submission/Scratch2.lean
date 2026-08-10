import FormalConjectures.Util.ProblemImports
open Nat Finset

def a (n : ℕ) : ℕ :=
  (Icc 1 n).filter (fun k => primeFactors k ⊆ primeFactors n) |>.card

#check mem_Icc
#check mem_filter
#check ext
#check card_pair
#check card_insert_of_not_mem
#check Nat.le_of_dvd
#check Nat.pos_of_dvd_of_pos
#check Nat.Prime.two_le
#check Nat.Prime.pos
#check Nat.Prime.ne_zero
#check Nat.Prime.ne_one
#check Nat.dvd_antisymm
#check Nat.eq_of_dvd_of_prime
#check Nat.Prime.eq_one_or_self_of_dvd
#check Nat.Prime.dvd_of_dvd_pow
#check Nat.exists_prime_and_dvd
#check Nat.prime_def_lt''
#check Nat.eq_of_le_of_lt_succ
#check Nat.succ_le_of_lt
#check Nat.lt_of_lt_of_le
#check Nat.le_antisymm
#check Nat.dvd_of_mod_eq_zero
#check Nat.le_of_dvd
#check Nat.one_mem_primeFactors
#check Nat.not_prime_one
#check Nat.primeFactors_one
#check Nat.Prime.primeFactors
