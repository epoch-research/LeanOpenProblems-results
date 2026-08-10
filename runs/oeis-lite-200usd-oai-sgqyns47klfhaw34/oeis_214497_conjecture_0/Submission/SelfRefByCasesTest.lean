import FormalConjectures.Util.ProblemImports

theorem t : False := by
  by_cases h : False
  · exact h
  · exact False.elim (h t)

theorem u (n : Nat) : False := by
  by_cases h : False
  · exact h
  · exact False.elim (h (u n))

#print axioms t
#print axioms u
