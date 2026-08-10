import FormalConjectures.Util.ProblemImports
open Nat BigOperators
instance : Fact (Nat.Prime 3) := by constructor; norm_num
noncomputable def xi_3 : Padic 3 := tsum (fun k : ℕ => (Nat.factorial k : Padic 3))
open Algebra
#check IsAlgebraic
#print IsAlgebraic
#check Algebra.IsAlgebraic
#print Algebra.IsAlgebraic
#check isAlgebraic_iff
#check Polynomial.aeval
#check Padic
#check Padic.instNormedField
#check Padic.ofRat
#check algebraMap ℚ (Padic 3)
#synth Algebra ℚ (Padic 3)
#check Algebraic.countable
#check exists_not_isAlgebraic
#check exists_transcendental
#check Transcendental
#check transcendental_iff_not_isAlgebraic
#check IsAlgebraic.isIntegral
#check IsIntegral.isAlgebraic
#check isAlgebraic_zero
#check isAlgebraic_nat
#check isAlgebraic_rat
#check IsAlgebraic.of_finite
#check Algebra.IsAlgebraic.isAlgebraic
#check IntermediateField.adjoin.algebraic
#eval approx_3_adic_sum_factorial 1
