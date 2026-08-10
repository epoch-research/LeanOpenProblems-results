import FormalConjectures.Util.ProblemImports
example : False := by
  letI : Field ℤ := Classical.choice (Infinite.nonempty_field (α := ℤ))
  exact Int.not_isField (inferInstance : IsField ℤ)
