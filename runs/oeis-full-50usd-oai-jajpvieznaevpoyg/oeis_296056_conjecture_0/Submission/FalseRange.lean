import FormalConjectures.Util.ProblemImports

example : ¬ ((1/2 : ℚ) ∈ Set.range (Int.cast : ℤ → ℚ)) := by
  rintro ⟨z, hz⟩
  norm_num at hz

-- example : ((1/2 : ℚ) ∈ Set.range (Int.cast : ℤ → ℚ)) := by simp
