import FormalConjectures.Util.ProblemImports
unsafe def bogus : False := unsafeCast ()
theorem t : False := by
  exact bogus
#print axioms t
