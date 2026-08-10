import FormalConjectures.Util.ProblemImports

partial def badDec2 (P : Prop) : Decidable P :=
  Decidable.isTrue (by
    exact Decidable.of_not_not (by intro h; exact h (by haveI : Decidable P := badDec2 P; exact of_decide_eq_true (show decide P = true by rfl))))

theorem arbitrary2 (P : Prop) : P := by
  haveI : Decidable P := badDec2 P
  exact of_decide_eq_true (show decide P = true by rfl)

#print axioms badDec2
#print axioms arbitrary2
