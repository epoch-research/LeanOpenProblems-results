import FormalConjectures.Util.ProblemImports
instance : Fact (Nat.Prime 3) := by constructor; norm_num

noncomputable instance selfAlg : Algebra.IsAlgebraic ℚ (Padic 3) := by
  letI : Algebra.IsAlgebraic ℚ (Padic 3) := selfAlg
  exact ⟨fun x => Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x⟩

example (x : Padic 3) : IsAlgebraic ℚ x := Algebra.IsAlgebraic.isAlgebraic x
#print axioms selfAlg
