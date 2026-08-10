import FormalConjectures.Util.ProblemImports

variable (P : Prop)

theorem test_eq_em : (True ∨ ¬ P) = (P ∨ ¬ P) := by
  apply propext
  constructor
  · intro _
    by_cases hP : P
    · exact Or.inl hP
    · exact Or.inr hP
  · intro _
    exact Or.inl trivial

#print axioms test_eq_em
