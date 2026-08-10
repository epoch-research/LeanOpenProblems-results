import FormalConjectures.Util.ProblemImports
open Nat BigOperators
instance : Fact (Nat.Prime 3) := by constructor; norm_num
#check PadicInt.norm_le_one
#check PadicInt.exists_eq
#check PadicInt.mk
#check IsIntegral.isAlgebraic
#check IsIntegral.algebraMap
#check IsFractionRing.isAlgebraic_iff
#synth IsFractionRing (PadicInt 3) (Padic 3)
#synth Algebra.IsIntegral ℤ (PadicInt 3)
#synth Algebra.IsAlgebraic ℚ (Padic 3)
