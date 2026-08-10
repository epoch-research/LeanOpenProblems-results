import FormalConjectures.Util.ProblemImports

theorem false_by_answer : False := by
  exact answer(sorry)
#print false_by_answer
#print axioms false_by_answer

theorem any_by_answer (P : Prop) : P := by
  exact answer(sorry)
#print axioms any_by_answer
