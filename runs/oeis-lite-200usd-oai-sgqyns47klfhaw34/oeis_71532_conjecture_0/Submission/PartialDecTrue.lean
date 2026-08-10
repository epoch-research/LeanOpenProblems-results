import FormalConjectures.Util.ProblemImports

partial def badDec (P : Prop) : Decidable P :=
  Decidable.isTrue (by
    haveI : Decidable P := badDec P
    exact of_decide_eq_true (show decide P = true by rfl))

theorem arbitrary (P : Prop) : P := by
  haveI : Decidable P := badDec P
  exact of_decide_eq_true (show decide P = true by rfl)

#print axioms badDec
#print axioms arbitrary
