import FormalConjectures.Util.ProblemImports

noncomputable def bad : False := by
  classical
  by_cases h : False
  · exact h
  · exact False.elim (h bad)

#print axioms bad
