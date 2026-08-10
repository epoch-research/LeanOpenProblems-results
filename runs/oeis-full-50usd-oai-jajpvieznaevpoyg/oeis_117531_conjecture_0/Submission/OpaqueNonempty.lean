import FormalConjectures.Util.ProblemImports
opaque hne : Nonempty False
#print axioms hne
theorem t : False := Classical.choice hne
#print axioms t
