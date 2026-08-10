import FormalConjectures.Util.ProblemImports

theorem test_answer_prop : True := by
  have h : Prop := answer(sorry)
  trivial

#print axioms test_answer_prop

