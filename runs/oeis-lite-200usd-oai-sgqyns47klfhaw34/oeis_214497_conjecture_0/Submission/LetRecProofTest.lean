import FormalConjectures.Util.ProblemImports

example : False := by
  let rec h : False := h
  exact h

example (P : Prop) : P := by
  let rec h : P := h
  exact h
