import FormalConjectures.Util.ProblemImports

example : (1 : ℚ) ∈ Set.range (Int.cast : ℤ → ℚ) := by
  exact ⟨1, by norm_num⟩
