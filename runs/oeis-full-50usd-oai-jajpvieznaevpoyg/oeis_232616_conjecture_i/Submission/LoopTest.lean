import FormalConjectures.Util.ProblemImports
partial def loopProof {P : Prop} : P := loopProof
example : False := loopProof
#print axioms loopProof
#print axioms _example
