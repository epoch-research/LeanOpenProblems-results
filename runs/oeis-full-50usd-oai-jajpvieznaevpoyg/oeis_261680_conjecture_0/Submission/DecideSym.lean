import FormalConjectures.Util.ProblemImports
example (n : Nat) : n + 1 > 0 := by
  exact of_decide_eq_true rfl
example (n : Nat) : n > 0 := by
  exact of_decide_eq_true rfl
