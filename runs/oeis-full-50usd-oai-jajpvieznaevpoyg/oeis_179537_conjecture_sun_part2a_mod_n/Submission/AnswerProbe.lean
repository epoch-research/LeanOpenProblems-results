import FormalConjectures.Util.ProblemImports
#check (answer(sorry) : Prop)
example : (answer(sorry) : Prop) := by trivial
#print axioms _example
-- Try exact answer(sorry) for a proposition proof
example : 1 = 1 := by exact answer(sorry)
#print axioms _example_1
