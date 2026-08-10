import FormalConjectures.Util.ProblemImports

example : False := by
  have h := Real.nthRoot_pow (n:=2) (-1 : ℝ) (by left; constructor <;> norm_num)
  norm_num [Real.nthRoot] at h

example : False := by
  have h := Real.pow_nthRoot (n:=2) (-1 : ℝ) (by left; constructor <;> norm_num)
  norm_num [Real.nthRoot] at h
