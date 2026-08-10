import FormalConjectures.Util.ProblemImports

example : False := by
  letI badFact : Fact False := ⟨by exact fact_iff.mp (inferInstance : Fact False)⟩
  exact fact_iff.mp (inferInstance : Fact False)
