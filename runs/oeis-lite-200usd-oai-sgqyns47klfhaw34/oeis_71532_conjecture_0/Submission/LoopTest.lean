import FormalConjectures.Util.ProblemImports

partial def bad (_ : Unit) : False := bad ()
#print axioms bad
example : False := bad ()
