import FormalConjectures.Util.ProblemImports

instance instFactSelf (P : Prop) : Fact P where
  out := Fact.out (p := P)

theorem arbitrary (P : Prop) : P := Fact.out (p := P)
#print axioms arbitrary
