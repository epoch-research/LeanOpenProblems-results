import FormalConjectures.Util.ProblemImports
partial instance instAnyInh (P : Prop) : Inhabited P := instAnyInh P
#print axioms instAnyInh
example (P : Prop) : P := default
#print axioms PartialInstanceSyntax._example_1
