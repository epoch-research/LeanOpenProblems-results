import FormalConjectures.Util.ProblemImports

instance badFact (P : Prop) : Fact P := by
  exact inferInstance

example : False := by
  exact (inferInstance : Fact False).out
#print axioms _example
