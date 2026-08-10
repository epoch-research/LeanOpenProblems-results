import FormalConjectures.Util.ProblemImports

example : False := by
  exact answer(sorry)

example : False := by
  change answer(sorry)
  trivial

example : (answer(sorry) : Prop) := by
  trivial

#print axioms _example
