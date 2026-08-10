import FormalConjectures.Util.ProblemImports
open Polynomial
example : (1 : ℚ[X]).coeff 1 = 0 := by
  rw [show (1 : ℚ[X]) = C (1 : ℚ) by rfl]
  rw [coeff_C]
  simp
example : (1 : ℚ[X]).coeff 1 = 0 := by
  change (C (1 : ℚ)).coeff 1 = 0
  rw [coeff_C]
  simp
#check coeff_one
