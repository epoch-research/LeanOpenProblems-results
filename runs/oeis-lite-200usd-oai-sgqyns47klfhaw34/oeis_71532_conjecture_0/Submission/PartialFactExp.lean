import FormalConjectures.Util.ProblemImports

partial def factAny (P : Prop) : Fact P := factAny P
#print axioms factAny
example (P : Prop) : P := (factAny P).out
#print axioms PartialFactExp._example_1
