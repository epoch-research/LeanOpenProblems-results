import FormalConjectures.Util.ProblemImports

-- Direct recursive instance via inferInstance
instance badFactFalse : Fact False := inferInstance
example : False := Fact.out (p := False)
#print axioms badFactFalse

-- Direct structure recursion
instance badFactFalse2 : Fact False where
  out := Fact.out (p := False)
example : False := Fact.out (p := False)
#print axioms badFactFalse2
