import FormalConjectures.Util.ProblemImports

example : True := by exact answer(sorry)
#print axioms _example

example : False := by
  exact answer(sorry)

example (P : Prop) : P := by
  exact answer(sorry)
