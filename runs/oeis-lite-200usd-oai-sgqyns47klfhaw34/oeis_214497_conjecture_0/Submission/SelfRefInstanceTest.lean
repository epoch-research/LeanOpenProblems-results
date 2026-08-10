import FormalConjectures.Util.ProblemImports

instance badFactSelf : Fact False where
  out := badFactSelf.out

#print axioms badFactSelf
example : False := Fact.out (p := False)
