import FormalConjectures.Util.ProblemImports

theorem t1 : False := by
  let rec h : False := h
  exact h

-- def with where recursive proof
noncomputable def bad : False := h where
  h : False := h

theorem t2 : False := bad
#print axioms t1
#print axioms t2
