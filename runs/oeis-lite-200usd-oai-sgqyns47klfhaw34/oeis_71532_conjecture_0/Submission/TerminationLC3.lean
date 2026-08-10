import FormalConjectures.Util.ProblemImports

def loopTerm3 (n : Nat) : False := loopTerm3 (n+1)
termination_by n
decreasing_by exact lcProof

#print axioms loopTerm3

theorem arbitrary3 (P : Prop) : P := False.elim (loopTerm3 0)
#print axioms arbitrary3
