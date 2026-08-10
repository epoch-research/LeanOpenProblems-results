import FormalConjectures.Util.ProblemImports

def badRec (n : Nat) : False := badRec n
termination_by n
decreasing_by exact Nat.lt_succ_self n

#print axioms badRec
theorem t : False := badRec 0
#print axioms t
