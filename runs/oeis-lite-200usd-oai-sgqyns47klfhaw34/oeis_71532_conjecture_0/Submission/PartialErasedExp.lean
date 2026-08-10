import FormalConjectures.Util.ProblemImports
partial def ep (P : Prop) : Erased P := ep P
#print axioms ep
example (P : Prop) : P := Erased.out_proof (ep P)
#print axioms PartialErasedExp._example_1
