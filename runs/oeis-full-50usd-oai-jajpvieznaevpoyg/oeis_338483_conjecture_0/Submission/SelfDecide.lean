import FormalConjectures.Util.ProblemImports

theorem Tself : False := by
  letI : Decidable False := isTrue Tself
  exact of_decide_eq_true rfl
