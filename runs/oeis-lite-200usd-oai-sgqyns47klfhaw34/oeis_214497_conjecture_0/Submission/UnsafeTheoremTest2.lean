import FormalConjectures.Util.ProblemImports

unsafe theorem badUnsafe2 : False := by
  exact lcProof

#print axioms badUnsafe2

example : False := badUnsafe2
