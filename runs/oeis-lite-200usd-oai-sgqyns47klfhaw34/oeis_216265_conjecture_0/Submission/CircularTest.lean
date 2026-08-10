import FormalConjectures.Util.ProblemImports

-- Direct self-reference in theorem body?
theorem circ1 : False := by
  exact circ1

#print axioms circ1

-- Mutual self-reference?
theorem circ2 : False := by
  exact circ3

theorem circ3 : False := by
  exact circ2

#print axioms circ2
#print axioms circ3
