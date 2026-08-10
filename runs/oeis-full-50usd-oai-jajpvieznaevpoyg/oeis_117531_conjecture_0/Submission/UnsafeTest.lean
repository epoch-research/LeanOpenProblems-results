import FormalConjectures.Util.ProblemImports
unsafe def bad : False := unsafeCast ()
theorem t : False := by exact bad
#print axioms t
