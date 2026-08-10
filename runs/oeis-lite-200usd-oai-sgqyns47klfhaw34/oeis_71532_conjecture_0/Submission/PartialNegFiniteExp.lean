import FormalConjectures.Util.ProblemImports
partial def nf (h : Finite Empty) : False := nf h
#print axioms nf
instance infEmpty : Infinite Empty where not_finite := nf
#print axioms infEmpty
example : False := by cases (Classical.choice (Infinite.nonempty Empty))
#print axioms PartialNegFiniteExp._example_1
