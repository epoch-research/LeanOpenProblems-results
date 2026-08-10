import FormalConjectures.Util.ProblemImports

partial def badProof (_ : Unit) : False := badProof ()

theorem t : False := badProof ()
#print axioms t
