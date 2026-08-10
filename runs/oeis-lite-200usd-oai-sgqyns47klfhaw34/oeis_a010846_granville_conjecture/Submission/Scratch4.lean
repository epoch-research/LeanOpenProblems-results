import FormalConjectures.Util.ProblemImports
open Nat Finset

#check Nat.ceil
#check Int.ceil
#check Nat.ceil_lt
#check Nat.lt_ceil
#check Nat.le_ceil
#check Nat.ceil_le
#check le_nat_ceil
#check nat_ceil_le
#check Nat.cast_lt
#check Nat.cast_le
#check Nat.cast_add
#check Nat.cast_max
#check max_le_iff
#check le_max_left
#check le_max_right
#check lt_of_lt_of_le
#check lt_of_le_of_lt
#check lt_of_lt_of_le
#check_mod_cast (show ((Nat.ceil (Real.exp 4) + 1 : ℕ) : ℝ) > Real.exp 4 from by exact Nat.lt_ceil.mp sorry)
