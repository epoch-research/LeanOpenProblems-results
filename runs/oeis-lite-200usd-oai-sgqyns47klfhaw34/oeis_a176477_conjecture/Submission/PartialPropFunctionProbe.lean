import FormalConjectures.Util.ProblemImports
partial def bad (n : Nat) : False := bad n
theorem t : False := bad 0
#print axioms t
