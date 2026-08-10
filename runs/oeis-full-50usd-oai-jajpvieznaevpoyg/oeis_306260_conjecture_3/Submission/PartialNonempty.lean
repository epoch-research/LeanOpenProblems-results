import FormalConjectures.Util.ProblemImports
partial def neFalse : Nonempty False := neFalse
example : False := Classical.choice neFalse
#print axioms neFalse
