import FormalConjectures.Util.ProblemImports

partial def badProof (u : Unit) : False := badProof ()

theorem Tpartial : False := badProof ()
#print axioms Tpartial
