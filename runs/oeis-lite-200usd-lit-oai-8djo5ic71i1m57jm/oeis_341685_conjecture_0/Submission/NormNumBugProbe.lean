import FormalConjectures.Util.ProblemImports

example : (0 : ℝ) ≤ -1 := by norm_num
example : False := by
  have h : (0 : ℝ) ≤ -1 := by norm_num
  linarith

example : False := by
  have h := Real.nthRoot_pow (n := 2) (-1) (Or.inl ⟨by norm_num, by norm_num⟩)
  have h1 : Real.nthRoot 2 ((-1 : ℝ) ^ 2) = 1 := by
    norm_num [Real.nthRoot, Real.rpow_natCast]
  linarith

#print axioms NormNumBugProbe._example_1
#print axioms NormNumBugProbe._example_2
