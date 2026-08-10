import FormalConjectures.Util.ProblemImports

example : False := by grind
example : False := by omega
example : False := by norm_num
example : (0:ℕ) = 1 := by grind
example : (0:ℤ) = 1 := by omega
example : (0:ℝ) = 1 := by norm_num
