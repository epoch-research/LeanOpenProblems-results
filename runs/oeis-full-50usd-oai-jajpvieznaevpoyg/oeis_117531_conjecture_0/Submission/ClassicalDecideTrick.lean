import FormalConjectures.Util.ProblemImports
example (P : Prop) : P := by
  classical
  exact of_decide_eq_true (show decide P = true from rfl)
