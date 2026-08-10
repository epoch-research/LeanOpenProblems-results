import FormalConjectures.Util.ProblemImports

section
variable (P : Prop)

noncomputable instance selfFact : Fact P := ⟨Fact.out⟩

example : P := by
  exact Fact.out

#print axioms selfFact
end
