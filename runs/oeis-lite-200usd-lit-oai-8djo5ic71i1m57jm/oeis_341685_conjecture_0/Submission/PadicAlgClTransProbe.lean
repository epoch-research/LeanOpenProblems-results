import FormalConjectures.Util.ProblemImports
open Nat BigOperators
instance : Fact (Nat.Prime 3) := by constructor; norm_num
#check PadicAlgCl
#synth Algebra ℚ (PadicAlgCl 3)
#synth IsScalarTower ℚ (Padic 3) (PadicAlgCl 3)
#synth Algebra.IsAlgebraic (Padic 3) (PadicAlgCl 3)
#synth Algebra.IsAlgebraic ℚ (PadicAlgCl 3)
#synth Algebra.IsAlgebraic ℚ (Padic 3)
