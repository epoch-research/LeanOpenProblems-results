import FormalConjectures.Util.ProblemImports
open Polynomial
#check coeff_one
#check Polynomial.coeff_one
#check coeff_C

example : ((1 : ℚ[X]).coeff 1) = 0 := by
  simp
