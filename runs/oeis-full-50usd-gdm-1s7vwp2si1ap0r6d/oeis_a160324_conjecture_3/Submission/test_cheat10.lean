import FormalConjectures.Util.ProblemImports

theorem test_thm : True := by
  have h : (answer(sorry) : Prop) := trivial
  exact h

#print axioms test_thm
