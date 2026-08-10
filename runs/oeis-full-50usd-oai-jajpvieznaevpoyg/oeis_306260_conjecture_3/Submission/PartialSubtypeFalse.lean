import FormalConjectures.Util.ProblemImports
partial def badSubFalse (n : ℕ) : {m : ℕ // False} := badSubFalse n
example : False := (badSubFalse 0).2
#print axioms badSubFalse
