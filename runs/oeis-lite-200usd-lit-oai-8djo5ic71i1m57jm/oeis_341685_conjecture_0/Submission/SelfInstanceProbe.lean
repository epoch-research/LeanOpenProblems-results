import FormalConjectures.Util.ProblemImports
instance : Fact (Nat.Prime 3) := by constructor; norm_num

noncomputable instance selfAlg : Algebra.IsAlgebraic ℚ (Padic 3) where
  isAlgebraic x := by
    exact Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x

example (x : Padic 3) : IsAlgebraic ℚ x := Algebra.IsAlgebraic.isAlgebraic x
#print axioms selfAlg
