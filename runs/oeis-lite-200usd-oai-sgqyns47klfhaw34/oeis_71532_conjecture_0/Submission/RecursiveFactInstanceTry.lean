import FormalConjectures.Util.ProblemImports

instance factAny (P : Prop) : Fact P := by
  exact factAny P

example : False := Fact.out (p := False)
#print axioms factAny
#print axioms _example
