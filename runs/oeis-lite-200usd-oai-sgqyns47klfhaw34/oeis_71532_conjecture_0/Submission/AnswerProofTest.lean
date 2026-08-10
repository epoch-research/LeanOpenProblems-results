import FormalConjectures.Util.ProblemImports

set_option google.answer always_true

theorem bad : False := by
  exact answer(sorry)

#print axioms bad
