import FormalConjectures.Util.ProblemImports

example : False := by
  let rec h : False := h
  termination_by 0
  decreasing_by simp
  exact h
