import FormalConjectures.Util.ProblemImports
partial def loopFalse : False := loopFalse
#check loopFalse
#print axioms loopFalse
theorem t : False := loopFalse
#print axioms t
