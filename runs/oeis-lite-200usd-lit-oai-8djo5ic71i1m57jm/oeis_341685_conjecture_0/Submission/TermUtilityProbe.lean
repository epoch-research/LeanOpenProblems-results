import FormalConjectures.Util.ProblemImports
#check answer(True)
#check (answer(sorry) : Prop)
#check (show Prop from answer(sorry))
example : (answer(sorry) : Prop) := by trivial
#print axioms _example
