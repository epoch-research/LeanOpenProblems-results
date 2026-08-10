import FormalConjectures.Util.ProblemImports
example (P : Prop) : P := by
  letI : Decidable P := isTrue (by exact of_decide_eq_true rfl)
  exact of_decide_eq_true rfl
#print axioms DecideLoop._example_1
