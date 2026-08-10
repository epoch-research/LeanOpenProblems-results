import FormalConjectures.Util.ProblemImports

theorem t : True := by
  classical
  by_contra h
  exact h t
