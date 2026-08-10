import FormalConjectures.Util.ProblemImports
example : (2:ℝ) ≤ 1 := by
  apply?
example : (1:ℕ) = 0 := by
  apply?
example : False := by
  have h : (2:ℝ) ≤ 1 := by apply?
  norm_num at h
