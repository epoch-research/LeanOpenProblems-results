import FormalConjectures.Util.ProblemImports
open Polynomial
instance : Fact (Nat.Prime 3) := by constructor; norm_num

#synth Algebra ℚ[X] (Padic 3 → Padic 3)
#check Algebra.IsAlgebraic
#check Algebra.IsAlgebraic.isAlgebraic
#check isAlgebraic_algebraMap
#check Algebra.IsAlgebraic.of_finite
#check Pi.algebra
#check Pi.ringHom

example (f : Padic 3 → Padic 3) : IsAlgebraic ℚ[X] f := by
  -- try known theorem
  infer_instance

example (x : Padic 3) : IsAlgebraic ℚ[X] x := by
  -- under algebra? there is no Algebra ℚ[X] (Padic 3)
  infer_instance
