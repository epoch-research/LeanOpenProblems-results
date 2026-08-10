import FormalConjectures.Util.ProblemImports

def bad (n : Nat) : False := bad (n+1)
termination_by n
decreasing_by
  exact False.elim (bad (n+1))

#print axioms bad
example : False := bad 0
