import FormalConjectures.Util.ProblemImports

example (P : Prop) [Decidable P] : P := by
  exact of_decide_eq_true rfl
