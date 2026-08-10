import FormalConjectures.Util.ProblemImports
example : False := by
  exact Classical.choice (show Nonempty False from inferInstance)
