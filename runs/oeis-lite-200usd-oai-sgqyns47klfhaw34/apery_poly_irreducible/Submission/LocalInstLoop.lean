import FormalConjectures.Util.ProblemImports
example (P : Prop) : P := by
  letI : Fact P := ⟨(inferInstance : Fact P).out⟩
  exact (inferInstance : Fact P).out
