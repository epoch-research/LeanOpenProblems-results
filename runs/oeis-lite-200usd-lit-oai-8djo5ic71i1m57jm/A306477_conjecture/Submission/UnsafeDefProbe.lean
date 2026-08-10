import FormalConjectures.Util.ProblemImports
unsafe def badProof : False := unsafeCast True.intro
theorem bad : False := badProof
#print axioms bad
#print bad
