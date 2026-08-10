import FormalConjectures.Util.ProblemImports

-- Try deriving simple contradictions from suspect custom theorems.
example : False := by
  have h := Real.nthRoot_of_even (n := 2) (by omega : Even 2) (-1)
  norm_num at h

example : False := by
  have h := Real.nthRoot_pow (n := 2) (-1) (Or.inl ⟨by norm_num, by norm_num⟩)
  norm_num at h

example : False := by
  have h := iteratedLog_two
  norm_num [Real.iteratedLog] at h
