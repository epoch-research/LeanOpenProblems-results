import FormalConjectures.Util.ProblemImports

example (P : Prop) : P := by
  have h : P := h
  exact h

example (P : Prop) : P := by
  let h : P := h
  exact h

example (P : Prop) : P := by
  suffices h : P from h
  exact h
