import FormalConjectures.Util.ProblemImports

partial def loopFalse (u : Unit) : False := loopFalse ()
#print axioms loopFalse

theorem t1 : False := loopFalse ()
#print axioms t1
