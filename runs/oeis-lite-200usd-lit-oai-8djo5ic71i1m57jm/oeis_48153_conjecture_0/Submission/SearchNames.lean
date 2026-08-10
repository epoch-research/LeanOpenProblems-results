import FormalConjectures.Util.ProblemImports

#check Nat.sum_range_mod
#check Nat.sum_range_mod_of_dvd
#check Finset.sum_range_id
#check Finset.sum_range_pow_two
#check Nat.mod_lt
#check Nat.mod_eq_of_lt
#check Nat.div_eq_of_lt
#check ZMod.sum_mul_div_add_sum_mul_div_eq_mul

open Finset

def A048153 (n : ℕ) : ℕ := Finset.sum (Finset.range n) (fun k => k ^ 2 % n)

example (n : ℕ) (h : 1 ≤ n) : A048153 n ≤ (n ^ 2 - 1) / 2 := by
  unfold A048153
  exact?
