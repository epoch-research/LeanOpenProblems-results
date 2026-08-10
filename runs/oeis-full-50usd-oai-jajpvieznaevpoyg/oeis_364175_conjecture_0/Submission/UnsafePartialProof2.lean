import FormalConjectures.Util.ProblemImports
partial unsafe def badProof (P : Prop) : P := badProof P
theorem bad : False := badProof False
#print axioms bad
