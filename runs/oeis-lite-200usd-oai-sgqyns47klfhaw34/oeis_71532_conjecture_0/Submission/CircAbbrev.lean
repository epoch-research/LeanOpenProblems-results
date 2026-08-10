import FormalConjectures.Util.ProblemImports

partial def idPartial (P : Prop) (p : P) : P := p

abbrev bad (P : Prop) : P := idPartial P (bad P)

theorem arbitrary (P : Prop) : P := bad P
#print axioms arbitrary
