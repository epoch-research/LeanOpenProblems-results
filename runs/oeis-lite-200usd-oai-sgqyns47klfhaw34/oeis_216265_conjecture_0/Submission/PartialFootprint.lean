import FormalConjectures.Util.ProblemImports

partial def loopFalse : False := loopFalse
#print axioms loopFalse

opaque opFalse : False
#print axioms opFalse

theorem t1 : False := loopFalse
#print axioms t1
