import FormalConjectures.Util.ProblemImports

def loopProof {P : Prop} (h : P) : False := loopProof h

def loopNot {P : Prop} (h : P → False) : False := loopNot h

#print axioms loopProof
#print axioms loopNot
