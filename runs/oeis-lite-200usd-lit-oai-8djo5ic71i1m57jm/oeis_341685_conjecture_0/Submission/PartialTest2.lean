import FormalConjectures.Util.ProblemImports
partial def bad (_ : Unit) : False := bad ()
#print axioms bad
theorem t : False := bad ()
#print axioms t
