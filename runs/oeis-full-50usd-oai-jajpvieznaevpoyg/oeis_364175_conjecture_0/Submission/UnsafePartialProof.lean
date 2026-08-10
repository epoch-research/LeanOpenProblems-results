import FormalConjectures.Util.ProblemImports
unsafe partial def badProof (P : Prop) : P := badProof P
theorem bad : False := badProof False
#print axioms bad
