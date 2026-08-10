import FormalConjectures.Util.ProblemImports
open Nat BigOperators
instance : Fact (Nat.Prime 3) := by constructor; norm_num
#synth Algebra ℤ (PadicInt 3)
#synth Algebra ℚ (PadicInt 3)
#synth Algebra.IsIntegral ℤ (PadicInt 3)
#synth Algebra.IsAlgebraic ℤ (PadicInt 3)
#synth Algebra.IsAlgebraic ℚ (PadicInt 3)
#check PadicInt
#check PadicInt.toPadic
#check PadicInt.coe
#check PadicInt.algebraMap_eq
#check PadicInt.isIntegral
