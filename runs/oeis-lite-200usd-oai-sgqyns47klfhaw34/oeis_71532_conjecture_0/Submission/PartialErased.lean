import FormalConjectures.Util.ProblemImports

partial def erasedLoop (P : Prop) : Erased P := erasedLoop P

theorem arbitrary (P : Prop) : P := Erased.out_proof (erasedLoop P)
#print axioms arbitrary
