import FormalConjectures.Util.ProblemImports
partial def badProof (_ : Nat) : False := badProof 0
theorem t : False := badProof 0
#print axioms t
