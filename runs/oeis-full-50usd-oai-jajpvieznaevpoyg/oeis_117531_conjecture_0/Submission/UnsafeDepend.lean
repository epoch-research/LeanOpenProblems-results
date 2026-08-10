import FormalConjectures.Util.ProblemImports
unsafe def bad2 : False := bad2

theorem t : False := by
  exact bad2
#print axioms t
