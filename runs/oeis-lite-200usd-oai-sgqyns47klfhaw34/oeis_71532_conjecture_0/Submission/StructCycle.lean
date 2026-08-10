import FormalConjectures.Util.ProblemImports

def bad : Nat → False
| 0 => bad 1
| n+1 => bad n

#print axioms bad
example : False := bad 0
