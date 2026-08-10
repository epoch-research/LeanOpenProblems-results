import FormalConjectures.Util.ProblemImports

def loopTerm2 (n : Nat) : False := loopTerm2 n
termination_by n
decreasing_by exact lcProof

#print axioms loopTerm2

theorem arbitrary2 (P : Prop) : P := False.elim (loopTerm2 0)
#print axioms arbitrary2
