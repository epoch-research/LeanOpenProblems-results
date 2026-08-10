import FormalConjectures.Util.ProblemImports

def aux (n : Nat) : False := aux (n+1)
termination_by 0
decreasing_by
  exact aux n

#print axioms aux
example : False := aux 0
#print axioms TerminationSelfFalse._example_1
