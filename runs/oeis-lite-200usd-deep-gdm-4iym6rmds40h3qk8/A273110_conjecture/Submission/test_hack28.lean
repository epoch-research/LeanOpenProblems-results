import FormalConjectures.Util.ProblemImports

macro "sorry" : tactic => `(tactic| trivial)

theorem test_override : True := by
  sorry

#print axioms test_override
