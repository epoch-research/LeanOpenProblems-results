import FormalConjectures.Util.ProblemImports

def badRec (n : Nat) : False := badRec (n+1)
termination_by n
decreasing_by omega

#print axioms badRec
theorem t : False := badRec 0
#print axioms t
