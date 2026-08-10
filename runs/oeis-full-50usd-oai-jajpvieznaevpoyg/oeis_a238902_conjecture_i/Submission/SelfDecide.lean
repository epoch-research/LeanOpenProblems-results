import FormalConjectures.Util.ProblemImports
theorem selfdec : False := by
  letI : Decidable False := isTrue selfdec
  exact of_decide_eq_true rfl
#print axioms selfdec
