import FormalConjectures.Util.ProblemImports

partial def badDecTrue (P : Prop) : Decidable P :=
  Decidable.isTrue (by
    let rec go (_ : Unit) : P := by
      cases badDecTrue P with
      | isTrue h => exact h
      | isFalse _ => exact go ()
    exact go ())

#print badDecTrue
#print axioms badDecTrue

example (P : Prop) : P := by
  haveI : Decidable P := badDecTrue P
  exact of_decide_eq_true rfl

#print axioms _example
