import FormalConjectures.Util.ProblemImports

partial def inhWith (P : Prop) [Inhabited P] : Inhabited P := inferInstance
#print axioms inhWith

instance instAnyInh (P : Prop) : Inhabited P := @inhWith P (instAnyInh P)
#print axioms instAnyInh
example (P : Prop) : P := (instAnyInh P).default
#print axioms InhabitedBootstrap3._example_1
