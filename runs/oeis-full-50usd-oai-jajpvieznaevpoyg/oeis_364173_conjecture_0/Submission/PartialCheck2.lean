import FormalConjectures.Util.ProblemImports
partial def bad (u : Unit) : False := bad u
#print axioms bad
example : False := bad ()
#print axioms _example
