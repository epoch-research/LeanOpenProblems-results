import FormalConjectures.Util.ProblemImports

theorem selfRecFalse : False := by
  let rec h : False := h
  exact h
#print axioms selfRecFalse
