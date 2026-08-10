import FormalConjectures.Util.ProblemImports

example : False := by
  aesop

example : False := by
  exact Classical.choice (show Nonempty False from inferInstance)
