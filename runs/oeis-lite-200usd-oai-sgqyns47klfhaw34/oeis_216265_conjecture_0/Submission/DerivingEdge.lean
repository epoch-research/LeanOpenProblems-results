import FormalConjectures.Util.ProblemImports

inductive E : Prop
  deriving Nonempty

#check (inferInstance : Nonempty E)
example : E := Classical.choice (inferInstance : Nonempty E)
#print axioms DerivingEdge._example_1

inductive T : Type
  deriving Nonempty
#check (inferInstance : Nonempty T)
