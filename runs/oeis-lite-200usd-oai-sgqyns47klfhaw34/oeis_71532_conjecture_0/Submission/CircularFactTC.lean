import FormalConjectures.Util.ProblemImports

instance (P : Prop) : Fact P where
  out := Fact.out (p := P)

example : False := Fact.out (p := False)
#print axioms instFact
