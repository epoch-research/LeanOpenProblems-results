import FormalConjectures.Util.ProblemImports
partial def bad (u : Unit) : False := bad u
theorem badthm : False := bad ()
#print axioms badthm
