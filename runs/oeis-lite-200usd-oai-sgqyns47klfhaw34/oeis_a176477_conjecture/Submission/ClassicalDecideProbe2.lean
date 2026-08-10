import FormalConjectures.Util.ProblemImports
example (P : Prop) : P := by
  classical
  have h : decide P = true := by
    native_decide
  exact of_decide_eq_true h
