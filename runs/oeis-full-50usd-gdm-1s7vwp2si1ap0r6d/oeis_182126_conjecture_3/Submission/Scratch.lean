import FormalConjectures.Util.ProblemImports

theorem my_test_thm : True := by
  let h_prop : Prop := answer(sorry)
  have h_true : h_prop := trivial
  exact h_true

#print axioms my_test_thm
