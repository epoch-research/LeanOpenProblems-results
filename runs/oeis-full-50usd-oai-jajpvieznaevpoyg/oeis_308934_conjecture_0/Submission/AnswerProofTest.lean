import FormalConjectures.Util.ProblemImports
theorem t1 : False := by
  exact answer(sorry)
theorem t2 : False := by
  change answer(sorry)
  trivial
#print axioms t1
#print axioms t2
