import FormalConjectures.Util.ProblemImports
instance : Fact (Nat.Prime 3) := by constructor; norm_num

open Module
#check Module.finrank_pos
#check FiniteDimensional.finrank_pos
#check Module.finrank_self
#check Module.finrank_eq_zero
#check Module.finrank_eq_zero_of_rank_eq_zero
#check Module.finrank_eq_zero_of_infinite_dimensional
#check Module.finite_of_finrank_pos
#check Module.finite_of_rank_eq_zero

example : 0 < Module.finrank ℚ (Padic 3) := by
  apply?
