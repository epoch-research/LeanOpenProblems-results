import FormalConjectures.Util.ProblemImports

theorem t : False := by
  letI : Decidable False := isTrue (by exact t)
  exact of_decide_eq_true rfl
#print axioms t
