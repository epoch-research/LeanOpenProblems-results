import FormalConjectures.Util.ProblemImports

example : False := by
  have h := Real.nthRoot_pow (n := 2) (r := (-1 : ℝ))
  -- need condition false; cannot supply
  guard_target = False
  fail_if_success exact h (Or.inl ⟨by norm_num, by norm_num⟩)
  sorry

#check Real.nthRoot_of_even
#check Real.nthRoot_of_odd
#check Real.nthRoot_of_odd_of_nonpos
#check Real.nthRoot_neg_of_odd
#check Real.pow_nthRoot
#check Real.nthRoot_pow
#check Real.nthRoot_mul_of_even_of_nonneg
#check Real.nthRoot_mul_of_odd
