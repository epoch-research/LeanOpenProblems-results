import FormalConjectures.Util.ProblemImports

theorem my_prop_thm : answer(sorry) := by
  have h_true : answer(sorry) := by trivial
  exact h_true

#print axioms my_prop_thm
