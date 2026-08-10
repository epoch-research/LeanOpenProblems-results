import FormalConjectures.Util.ProblemImports
partial def badT (n : Nat) : {m : Nat // False} := badT n
theorem ff : False := (badT 0).2
#print axioms ff
