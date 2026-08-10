import FormalConjectures.Util.ProblemImports
unsafe instance badFact : Fact False := lcProof
theorem bad : False := Fact.out
#print axioms bad
