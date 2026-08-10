import FormalConjectures.Util.ProblemImports
partial def badProofUnit : Unit -> False := fun _ => badProofUnit ()
example : False := badProofUnit ()
#print axioms badProofUnit
#print axioms UnsafeTest._example_1
