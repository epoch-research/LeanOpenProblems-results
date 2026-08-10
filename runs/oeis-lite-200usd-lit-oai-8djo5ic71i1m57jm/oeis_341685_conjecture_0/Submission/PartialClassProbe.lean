import FormalConjectures.Util.ProblemImports
instance : Fact (Nat.Prime 3) := by constructor; norm_num

partial noncomputable def algClass : Algebra.IsAlgebraic ℚ (Padic 3) := algClass
noncomputable instance : Algebra.IsAlgebraic ℚ (Padic 3) := algClass
example : IsAlgebraic ℚ (0 : Padic 3) := Algebra.IsAlgebraic.isAlgebraic _
#print axioms algClass
