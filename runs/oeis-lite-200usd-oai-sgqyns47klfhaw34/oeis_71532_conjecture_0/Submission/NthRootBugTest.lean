import FormalConjectures.Util.ProblemImports
open Real

#check nthRoot_of_even
#check nthRoot_of_odd
#check nthRoot_pow
#check pow_nthRoot

example : False := by
  have h := nthRoot_of_odd (n:=1) (r:=(-1:ℝ)) (by norm_num : Odd (1:ℕ))
  norm_num at h

#print axioms nthRoot_of_odd
#print axioms nthRoot_pow
