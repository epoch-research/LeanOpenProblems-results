import FormalConjectures.Util.ProblemImports
opaque p : False
#print axioms p
opaque q : False := by
  exact False.elim (by contradiction)
#print axioms q
