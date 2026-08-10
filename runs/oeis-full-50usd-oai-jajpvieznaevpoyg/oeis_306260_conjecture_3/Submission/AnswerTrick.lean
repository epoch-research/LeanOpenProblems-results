import FormalConjectures.Util.ProblemImports
example : False := by
  exact answer(sorry)
example : (answer(sorry) : Prop) := by trivial
#check (answer(sorry) : Prop)
