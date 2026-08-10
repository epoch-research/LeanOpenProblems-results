import FormalConjectures.Util.ProblemImports

partial def bad (_ : Unit) : False := bad ()

example : False := bad ()
#print axioms bad
#print axioms _example
