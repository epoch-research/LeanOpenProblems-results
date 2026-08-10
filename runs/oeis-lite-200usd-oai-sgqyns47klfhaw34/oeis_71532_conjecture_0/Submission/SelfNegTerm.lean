import FormalConjectures.Util.ProblemImports
axiom P : Prop

theorem dis : ¬ P := by
  intro h
  exact dis h
#print axioms dis

theorem dis2 : ¬ (P ∧ P) := by
  intro h
  exact dis2 ⟨h.1,h.1⟩
#print axioms dis2
