import FormalConjectures.Util.ProblemImports
example : (3/5 : ℝ) < Real.log 2 := by norm_num
example : Real.log 4 < (7/5 : ℝ) := by norm_num
example (n:ℕ) (hn:5000≤n) : Real.log (n:ℝ) ≤ 2 * Real.sqrt (n:ℝ) := by
  have := Real.log_le_rpow_div (x := (n:ℝ)) (ε := (1/2:ℝ)) (by positivity) (by norm_num)
  rw [Real.rpow_def_of_pos] at this
  sorry
