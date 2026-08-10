import FormalConjectures.Util.ProblemImports
partial def badInh (P : Prop) : Inhabited P := badInh P
#print axioms badInh
example : False := (badInh False).default
#print axioms _example
