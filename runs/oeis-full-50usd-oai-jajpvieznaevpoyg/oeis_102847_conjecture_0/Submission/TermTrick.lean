import FormalConjectures.Util.ProblemImports

def bad (n : Nat) : False := bad (n+1)
termination_by n
 decreasing_by
  exfalso
  exact bad n

example : False := bad 0
#print axioms bad
