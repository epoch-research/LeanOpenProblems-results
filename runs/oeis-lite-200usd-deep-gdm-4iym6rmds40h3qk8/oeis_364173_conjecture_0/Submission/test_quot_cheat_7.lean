import FormalConjectures.Util.ProblemImports

variable (P : Prop)

theorem test_eq : (True ∧ P) = (P ∧ P) := by
  apply propext
  constructor
  · intro h
    exact ⟨h.2, h.2⟩
  · intro h
    exact ⟨trivial, h.1⟩

#print axioms test_eq
