import FormalConjectures.Util.ProblemImports
open Algebra
instance : Fact (Nat.Prime 3) := by constructor; norm_num
#synth Algebra (Padic 3) (PadicAlgCl 3)
#synth Algebra ℚ (PadicAlgCl 3)
#synth IsScalarTower ℚ (Padic 3) (PadicAlgCl 3)
#synth Algebra.IsAlgebraic (Padic 3) (PadicAlgCl 3)
#synth Algebra.IsAlgebraic ℚ (PadicAlgCl 3)
#synth Algebra.IsAlgebraic ℚ (Padic 3)
example : Algebra.IsAlgebraic ℚ (Padic 3) := by
  exact Algebra.IsAlgebraic.tower_bot ℚ (Padic 3) (PadicAlgCl 3)
