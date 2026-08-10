import FormalConjectures.Util.ProblemImports

partial def loopProof (P : Prop) : P := loopProof P

#check loopProof
#print axioms loopProof

theorem bad : False := loopProof False
#print axioms bad
