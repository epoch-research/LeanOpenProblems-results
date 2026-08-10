import FormalConjectures.Util.ProblemImports
open Polynomial

#check FormalConjecturesForMathlib
#check Polynomial.instAlgebraPi
#print axioms Polynomial.instAlgebraPi

-- Try laws for R=ℤ, S=ℤ? Need Semiring? 
example : False := by
  -- use Algebra.smul_def? map_one? Try evaluate algebraMap of X?
  let f : ℤ[X] := 0
  norm_num
