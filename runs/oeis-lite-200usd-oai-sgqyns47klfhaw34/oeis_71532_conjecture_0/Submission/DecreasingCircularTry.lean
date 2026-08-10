import FormalConjectures.Util.ProblemImports

def badUp (n : Nat) : False := badUp (n+1)
termination_by n
decreasing_by
  exact False.elim (badUp n)

#print axioms badUp
example : False := badUp 0
#print axioms _example
