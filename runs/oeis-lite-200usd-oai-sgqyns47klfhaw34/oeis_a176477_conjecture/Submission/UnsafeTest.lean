import FormalConjectures.Util.ProblemImports
unsafe axiom bad : False
theorem t : False := by exact bad
#print axioms t
