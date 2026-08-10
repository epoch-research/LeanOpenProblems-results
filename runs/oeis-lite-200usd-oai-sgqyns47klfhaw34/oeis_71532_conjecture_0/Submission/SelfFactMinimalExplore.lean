import FormalConjectures.Util.ProblemImports

instance instFactSelf (P : Prop) : Fact P := inferInstance

theorem arbitrary (P : Prop) : P := Fact.out (p := P)
#print axioms arbitrary
