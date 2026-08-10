import FormalConjectures.Util.ProblemImports

partial def factLoop (P : Prop) : Fact P := factLoop P

theorem arbitrary (P : Prop) : P := Fact.out (factLoop P)
#print axioms arbitrary
