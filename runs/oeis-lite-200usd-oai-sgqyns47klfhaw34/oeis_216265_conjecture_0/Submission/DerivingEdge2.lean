import FormalConjectures.Util.ProblemImports

inductive E : Prop

#check (inferInstance : Nonempty E)
example : E := Classical.choice (inferInstance : Nonempty E)
#print axioms DerivingEdge2._example_1
