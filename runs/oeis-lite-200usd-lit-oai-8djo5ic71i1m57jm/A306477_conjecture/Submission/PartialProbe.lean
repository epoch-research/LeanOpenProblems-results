import FormalConjectures.Util.ProblemImports
partial def bad (P : Prop) : P := bad P
example : False := bad False
#print axioms bad
#print axioms PartialProbe._example_1
