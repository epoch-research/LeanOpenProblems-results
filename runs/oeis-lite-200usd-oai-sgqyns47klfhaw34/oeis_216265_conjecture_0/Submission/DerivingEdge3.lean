import FormalConjectures.Util.ProblemImports

inductive E : Prop

deriving instance Nonempty for E

#check (inferInstance : Nonempty E)
example : E := Classical.choice (inferInstance : Nonempty E)
#print axioms DerivingEdge3._example_1
