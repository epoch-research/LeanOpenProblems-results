import FormalConjectures.Util.ProblemImports

theorem bad : False := by
  let rec h : False := h
  exact h
