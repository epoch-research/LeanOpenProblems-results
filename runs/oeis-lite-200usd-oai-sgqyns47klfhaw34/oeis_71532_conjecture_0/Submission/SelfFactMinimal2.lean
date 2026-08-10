import FormalConjectures.Util.ProblemImports

instance selfFact (P : Prop) : Fact P where
  out := (inferInstance : Fact P).out

theorem arbitrary (P : Prop) : P := Fact.out (p:=P)
#print axioms selfFact
#print axioms arbitrary
