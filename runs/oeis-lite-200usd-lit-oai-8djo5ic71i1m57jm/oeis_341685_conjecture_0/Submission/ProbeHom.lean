import FormalConjectures.Util.ProblemImports
open Nat BigOperators Algebra
instance : Fact (Nat.Prime 3) := by constructor; norm_num

#synth Nonempty (Padic 3 →+* ℚ)
#synth Nonempty (ℚ →+* Padic 3)
#synth Nonempty (Padic 3 →ₐ[ℚ] ℚ)
#synth Nonempty (Padic 3 ≃ₐ[ℚ] ℚ)
#synth Algebra (Padic 3) ℚ
#synth Algebra ℚ (AlgebraicClosure ℚ)
#synth Nonempty (Padic 3 →ₐ[ℚ] AlgebraicClosure ℚ)
#synth Nonempty (Padic 3 →+* AlgebraicClosure ℚ)
