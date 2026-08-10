import FormalConjectures.Util.ProblemImports
open Google

theorem t1 : False := answer(sorry)
#print axioms t1

theorem t2 : answer(sorry) := by trivial
#check t2
#print t2
#print axioms t2
