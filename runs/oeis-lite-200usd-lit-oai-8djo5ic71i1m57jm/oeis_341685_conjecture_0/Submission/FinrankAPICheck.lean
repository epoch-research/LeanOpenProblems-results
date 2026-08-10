import FormalConjectures.Util.ProblemImports
#check FiniteDimensional.of_finrank_eq_succ
#check FiniteDimensional.of_finrank_eq_zero
#check FiniteDimensional.of_finrank_pos
#check Module.finite_of_rank_eq_zero
#check Module.finrank_eq_zero_of_rank_eq_zero
#check Module.finrank_of_infinite_dimensional
#check Module.finrank
#check Module.rank
#check Module.rank_pos_of_free
#check Module.rank_eq_zero
#check Module.rank_eq_zero_iff
#check Module.finrank_eq_rank
example : Module.finrank ℚ (Padic 3) = 0 := by simp [Module.finrank]
