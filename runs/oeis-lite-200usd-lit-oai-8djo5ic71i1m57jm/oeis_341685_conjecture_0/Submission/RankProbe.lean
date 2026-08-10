import FormalConjectures.Util.ProblemImports
instance : Fact (Nat.Prime 3) := by constructor; norm_num
#check Module.rank ℚ (Padic 3)
#check Module.rank_def
example : Module.rank ℚ (Padic 3) = 0 := by
  simp [Module.rank]
example : Module.Finite ℚ (Padic 3) := by
  exact Module.finite_of_rank_eq_zero (show Module.rank ℚ (Padic 3) = 0 by simp [Module.rank])
