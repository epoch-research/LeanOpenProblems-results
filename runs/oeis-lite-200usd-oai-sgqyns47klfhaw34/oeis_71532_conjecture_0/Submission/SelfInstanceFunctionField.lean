import FormalConjectures.Util.ProblemImports

instance infEmpty : Infinite Empty where
  not_finite := fun h => @Infinite.not_finite Empty infEmpty h
#print axioms infEmpty
example : Nonempty Empty := Infinite.nonempty Empty
#print axioms SelfInstanceFunctionField._example_1
example : False := by cases (Classical.choice (Infinite.nonempty Empty))
#print axioms SelfInstanceFunctionField._example_2
