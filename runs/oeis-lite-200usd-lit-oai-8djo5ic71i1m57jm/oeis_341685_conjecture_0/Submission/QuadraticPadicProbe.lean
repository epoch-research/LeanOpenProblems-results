import FormalConjectures.Util.ProblemImports
open Nat BigOperators
instance : Fact (Nat.Prime 3) := by constructor; norm_num
#check Algebra.IsQuadraticExtension
#synth Algebra.IsQuadraticExtension ℚ (Padic 3)
#check Algebra.IsQuadraticExtension.to_numberField
example : NumberField (Padic 3) := Algebra.IsQuadraticExtension.to_numberField (K := Padic 3)
