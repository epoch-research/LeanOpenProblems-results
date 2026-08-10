import FormalConjectures.Util.ProblemImports

partial def magicDecidable (P : Prop) : Decidable P :=
  Decidable.isTrue (by
    exact @of_decide_eq_true P (magicDecidable P) (by rfl))

example (P : Prop) : P := by
  exact @of_decide_eq_true P (magicDecidable P) (by rfl)

#print axioms magicDecidable
#print axioms _example
