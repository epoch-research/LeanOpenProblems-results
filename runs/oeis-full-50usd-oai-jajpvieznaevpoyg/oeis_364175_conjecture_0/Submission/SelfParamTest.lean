import FormalConjectures.Util.ProblemImports

theorem selfParam (n : Nat) : True := by
  exact selfParam n

-- with a false branch only
theorem selfByCases (P : Prop) : P := by
  by_cases h : P
  · exact h
  · exact False.elim (h (selfByCases P))
