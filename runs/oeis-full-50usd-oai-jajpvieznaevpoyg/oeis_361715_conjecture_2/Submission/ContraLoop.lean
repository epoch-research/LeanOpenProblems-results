import FormalConjectures.Util.ProblemImports

example : False := by
  by_contra h
  exact h (by_contra h)
