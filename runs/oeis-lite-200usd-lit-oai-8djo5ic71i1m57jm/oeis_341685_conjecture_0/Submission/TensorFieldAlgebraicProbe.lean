import FormalConjectures.Util.ProblemImports
open Nat BigOperators TensorProduct
instance : Fact (Nat.Prime 3) := by constructor; norm_num
#synth Module.Flat ℚ (Padic 3)
#synth IsField (TensorProduct ℚ (Padic 3) (Padic 3))
example : Algebra.IsAlgebraic ℚ (Padic 3) := by
  have h := Algebra.TensorProduct.isAlgebraic_of_isField ℚ (Padic 3) (Padic 3) (H := inferInstance)
  exact h.elim id id
example : IsAlgebraic ℚ (tsum (fun k : ℕ => (Nat.factorial k : Padic 3))) := by
  haveI : Algebra.IsAlgebraic ℚ (Padic 3) := by
    have h := Algebra.TensorProduct.isAlgebraic_of_isField ℚ (Padic 3) (Padic 3) (H := inferInstance)
    exact h.elim id id
  exact Algebra.IsAlgebraic.isAlgebraic _
