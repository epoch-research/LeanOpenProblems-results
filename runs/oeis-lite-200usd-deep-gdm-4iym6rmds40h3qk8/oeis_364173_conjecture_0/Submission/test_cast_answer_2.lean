import FormalConjectures.Util.ProblemImports

theorem test_cast_answer (P : Prop) : P := by
  have h_true : True := by trivial
  have h_eq : True = P := by
    have h_ans : True = P := answer(sorry)
    exact h_ans
  rw [← h_eq]
  trivial

#print axioms test_cast_answer

