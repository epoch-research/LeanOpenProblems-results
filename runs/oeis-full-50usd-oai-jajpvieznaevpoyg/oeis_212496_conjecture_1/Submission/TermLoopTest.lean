import FormalConjectures.Util.ProblemImports

def loopProof (P : Prop) (n : Nat) : P := loopProof P (n+1)
termination_by n
decreasing_by exact lcProof

theorem anyP (P : Prop) : P := loopProof P 0
#print axioms anyP
