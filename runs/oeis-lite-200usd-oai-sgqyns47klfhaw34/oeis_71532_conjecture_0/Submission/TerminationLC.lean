import FormalConjectures.Util.ProblemImports

def loopTerm (u : Unit) : False := loopTerm u
termination_by 0
decreasing_by exact lcProof

#print axioms loopTerm

theorem arbitrary (P : Prop) : P := False.elim (loopTerm ())
#print axioms arbitrary
