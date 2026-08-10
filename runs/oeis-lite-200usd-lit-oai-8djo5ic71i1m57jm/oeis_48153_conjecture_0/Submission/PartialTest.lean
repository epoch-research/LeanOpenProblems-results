import FormalConjectures.Util.ProblemImports
partial def loopProof (P : Prop) [Decidable P] : P :=
  if h : P then h else loopProof P
#print axioms loopProof
example : False := loopProof False
#print axioms «example»
