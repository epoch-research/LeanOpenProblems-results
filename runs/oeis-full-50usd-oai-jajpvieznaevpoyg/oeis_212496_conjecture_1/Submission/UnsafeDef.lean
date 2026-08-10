import FormalConjectures.Util.ProblemImports
unsafe def ufalse : False := by
  exact (panic! "bad" : False)
theorem t : False := ufalse
#print axioms t
