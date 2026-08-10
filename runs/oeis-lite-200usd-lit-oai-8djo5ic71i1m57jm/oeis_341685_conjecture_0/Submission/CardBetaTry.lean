import FormalConjectures.Util.ProblemImports
instance : Fact (Nat.Prime 3) := by constructor; norm_num
noncomputable abbrev Beta := FractionRing (MvPolynomial (Padic 3) ℚ)
example : Cardinal.mk (Padic 3) = Cardinal.mk Beta := by
  simp [Beta]
example : Nonempty ((Padic 3) ≃ Beta) := by
  exact Cardinal.eq.mp (by simp [Beta])
