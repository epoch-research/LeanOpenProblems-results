import FormalConjectures.Util.ProblemImports
open Polynomial

#check Polynomial.instAlgebraPi
#check algebraMap (ℚ[X]) (ℚ → ℚ)
#check (algebraMap (ℚ[X]) (ℚ → ℚ) Polynomial.X)
#check (algebraMap (ℚ[X]) (ℚ → ℚ) (Polynomial.C 1))

example : False := by
  -- if algebraMap sends X and C? test at 0/1
  have hX0 : (algebraMap (ℚ[X]) (ℚ → ℚ) Polynomial.X) 0 = (0 : ℚ) := by native_decide
  guard_target = False
  sorry
