import FormalConjectures.Util.ProblemImports
instance : Fact (Nat.Prime 3) := by constructor; norm_num
#check Module.finrank ℚ (Padic 3)
#check finrank
#check Module.finrank_zero_of_not_finiteDimensional
#check FiniteDimensional.of_finrank_eq_succ
#check FiniteDimensional.of_finrank_eq_zero
#check FiniteDimensional.of_finrank_pos
#check Module.finite_of_finrank_eq_succ
#check Module.finite_of_finrank_eq_zero
#check Module.finite_of_finrank_pos
example : Module.finrank ℚ (Padic 3) = 0 := by
  simp [Module.finrank]
example : FiniteDimensional ℚ (Padic 3) := by
  apply?
