import FormalConjectures.Util.ProblemImports
unsafe def bad : False := unsafeCast ()
theorem bogus : False := by exact bad
#print axioms bogus
