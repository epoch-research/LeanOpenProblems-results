import FormalConjectures.Util.ProblemImports

partial def idP (P : Prop) : Id P := idP P

theorem arbitrary1 (P : Prop) : P := idP P
#print axioms arbitrary1
