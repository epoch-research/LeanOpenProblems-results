import FormalConjectures.Util.ProblemImports

partial def bad : Nat → False := fun n => bad n
#print axioms bad
example : Nat → False := bad
