import FormalConjectures.Util.ProblemImports

instance instFactAny (P : Prop) : Fact P where
  out := Fact.out
#print axioms instFactAny
example (P : Prop) : P := Fact.out
#print axioms RecursiveFactExp._example_1
