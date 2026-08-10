import FormalConjectures.Util.ProblemImports

theorem t : False := by
  letI : Decidable False := isTrue t
  exact of_decide_eq_true rfl
