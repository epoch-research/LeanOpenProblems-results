import Submission.FakeMonoidFallback3
open Polynomial
#check coeff_C
#check Polynomial.coeff_C
example : (Polynomial.C (1 : ℚ)).coeff 1 = 0 := by
  rw [coeff_C]
  simp
