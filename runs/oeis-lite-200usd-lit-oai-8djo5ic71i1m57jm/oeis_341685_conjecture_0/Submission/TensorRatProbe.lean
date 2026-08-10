import FormalConjectures.Util.ProblemImports
open Nat BigOperators
instance : Fact (Nat.Prime 3) := by constructor; norm_num
noncomputable def xi_3 : Padic 3 := tsum (fun k : ℕ => (Nat.factorial k : Padic 3))
open Algebra

noncomputable def tensorRatIsField : IsField (TensorProduct ℚ (Padic 3) ℚ) := by
  exact ((Algebra.TensorProduct.rid ℚ ℚ (Padic 3)).toMulEquiv.isField (Field.toIsField _))

example : Algebra.IsAlgebraic ℚ (Padic 3) ∨ Algebra.IsAlgebraic ℚ ℚ := by
  exact Algebra.TensorProduct.isAlgebraic_of_isField ℚ (Padic 3) ℚ (H := tensorRatIsField)

example : IsAlgebraic ℚ xi_3 := by
  have h := Algebra.TensorProduct.isAlgebraic_of_isField ℚ (Padic 3) ℚ (H := tensorRatIsField)
  simp at h
  trace_state
  exact?
