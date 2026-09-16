axiom A : Prop
theorem foo : ¬ (A ∧ ¬ A) := by
  intro h
  exact h.2 h.1
#print axioms foo
