import FormalConjectures.Util.ProblemImports
instance : Fact (Nat.Prime 3) := by constructor; norm_num
open Algebra
#print Algebra.IsQuadraticExtension
#print NumberField
#check Algebra.IsQuadraticExtension.to_numberField
#check QuadraticAlgebra.instIsQuadraticExtension
#check NumberField.isAlgebraic
#check Algebra.IsQuadraticExtension.finrank_eq_two
#check Algebra.IsQuadraticExtension.exists_linearIndependent
#check Algebra.IsQuadraticExtension.instFiniteDimensional
#synth Algebra.IsQuadraticExtension ℚ (Padic 3)
