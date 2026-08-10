import FormalConjectures.Util.ProblemImports
instance : Fact (Nat.Prime 3) := ⟨by norm_num⟩
#synth Subsingleton (Algebra ℚ (Padic 3))
#check DivisionRing.toRatAlgebra
example (a : Algebra ℚ (Padic 3)) : a = inferInstance := by exact Subsingleton.elim _ _
