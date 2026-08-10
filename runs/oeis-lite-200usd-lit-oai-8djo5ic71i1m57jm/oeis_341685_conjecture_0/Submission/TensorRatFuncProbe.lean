import FormalConjectures.Util.ProblemImports
open Algebra
#check Algebra.TensorProduct.isAlgebraic_of_isField
#check RatFunc
#synth Algebra ℚ (RatFunc ℚ)
#synth IsField (TensorProduct ℚ (Padic 3) (RatFunc ℚ))
#synth Field (TensorProduct ℚ (Padic 3) (RatFunc ℚ))
#check Algebra.TensorProduct.comm ℚ (Padic 3) (RatFunc ℚ)
