import FormalConjectures.Util.ProblemImports
open Nat BigOperators
instance : Fact (Nat.Prime 3) := by constructor; norm_num
#synth Algebra ℚ (PadicInt 3)
#synth Algebra (PadicInt 3) (Padic 3)
#synth Algebra ℚ (Padic 3)
#synth IsScalarTower ℚ (PadicInt 3) (Padic 3)
#check PadicInt.norm_le_one
#check IsIntegral
#check isAlgebraic_iff_isIntegral

noncomputable def xi_3 : Padic 3 := tsum (fun k : ℕ => (Nat.factorial k : Padic 3))
example : ‖xi_3‖ ≤ 1 := by
  apply?
example : IsIntegral ℚ xi_3 := by
  apply?
