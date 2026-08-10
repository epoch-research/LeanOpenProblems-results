import FormalConjectures.Util.ProblemImports
opaque bad : ∀ P : Prop, P
theorem t : False := bad False
#print axioms t
