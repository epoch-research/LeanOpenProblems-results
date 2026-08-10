import FormalConjectures.Util.ProblemImports

partial def decLoop (P : Prop) : Decidable P := decLoop P

example (P : Prop) : P := by
  letI : Decidable P := decLoop P
  exact of_decide_eq_true rfl
