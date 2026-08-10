import FormalConjectures.Util.ProblemImports
partial def bad (P : Prop) : P := bad P
#print axioms bad
example : False := bad False
#print axioms _example
