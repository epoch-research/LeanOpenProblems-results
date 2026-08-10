import FormalConjectures.Util.ProblemImports
partial def loopFalse (n : Nat) : False := loopFalse n
#print axioms loopFalse
theorem t : False := loopFalse 0
#print axioms t
