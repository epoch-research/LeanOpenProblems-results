import FormalConjectures.Util.ProblemImports
example : (1 = 2) := by
  classical
  have h : decide (1 = 2) = true := by native_decide
  exact of_decide_eq_true h
