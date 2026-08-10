import FormalConjectures.Util.ProblemImports
open Algebra
instance : Fact (Nat.Prime 3) := by constructor; norm_num
#synth IsAlgClosed (Padic 3)
#synth Algebra.IsIntegral ℚ (Padic 3)
#synth Algebra.IsIntegral ℤ (Padic 3)
#synth IsIntegralClosure (Padic 3) ℚ (Padic 3)
#synth IsIntegralClosure ℤ ℚ (Padic 3)
#synth Algebra.FiniteType ℚ (Padic 3)
#synth Algebra.EssFiniteType ℚ (Padic 3)
#synth FormallyUnramified ℚ (Padic 3)
#synth FormallySmooth ℚ (Padic 3)
#check Algebra.finite_of_essFiniteType_of_isAlgebraic
#check IsAlgClosed.isAlgebraic
#check Algebra.IsAlgebraic.of_finite
#check Algebra.IsAlgebraic.tower_bot
#check IsAlgebraic.tower_top
