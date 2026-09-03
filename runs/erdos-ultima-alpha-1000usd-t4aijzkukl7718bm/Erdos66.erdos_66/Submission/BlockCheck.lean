import FormalConjecturesUtil
open scoped Classical
#check Nat.add_mul_div_left
#check Nat.mul_add_div
#check Nat.mul_add_div_left
#check Nat.sub_eq_iff_eq_add
#check Finset.sum_subset
#check Finset.sum_subset_zero_on_sdiff
#check Finset.sum_congr
#check Finset.sum_ite_mem
#check Finset.sum_boole
#check Finset.sum_bij
example (A : Set ℕ) (n : ℕ) : (if n ∈ A then 1 else 0 : ℕ) ≤ 1 := by split_ifs <;> omega
