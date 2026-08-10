import FormalConjectures.Util.ProblemImports

theorem test_cast_answer (P : Prop) : P := by
  have h_answer : Prop := answer(sorry)
  have h_true : h_answer := by trivial
  have h_eq : h_answer = P := by sorry
  rw [h_eq] at h_true
  exact h_true
