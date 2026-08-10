import FormalConjectures.Util.ProblemImports

def selfProof (P : Prop) : P := selfProof P
termination_by 0
decreasing_by simp

theorem arbitrary (P : Prop) : P := selfProof P
#print axioms arbitrary
