import FormalConjectures.Util.ProblemImports

example : False := by
  exact answer(sorry)

example : True := by
  exact answer(sorry)

#check (answer(sorry) : Prop)
