import FormalConjectures.Util.ProblemImports
theorem t1 : False := by
  exact unreachable!
#print axioms t1
theorem t2 : False := by
  exact panic! "bad"
#print axioms t2
