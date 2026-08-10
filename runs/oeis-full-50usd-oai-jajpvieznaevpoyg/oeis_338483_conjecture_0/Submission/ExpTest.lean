import FormalConjectures.Util.ProblemImports
#check Real.add_one_le_exp
#check Real.exp_le_exp
#check Real.exp_lt_exp
#check Real.exp_pos
example : Real.exp (1:ℝ) ≤ 3 := by
  nlinarith [Real.add_one_le_exp (1:ℝ)]
example : (2:ℝ) ≤ Real.exp 1 := by
  nlinarith [Real.add_one_le_exp (1:ℝ)]
