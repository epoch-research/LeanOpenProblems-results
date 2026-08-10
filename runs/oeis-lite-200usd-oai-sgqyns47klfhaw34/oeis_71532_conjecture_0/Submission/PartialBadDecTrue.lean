import FormalConjectures.Util.ProblemImports

mutual
  partial def badDecTrue (P : Prop) : Decidable P :=
    Decidable.isTrue (badProof P)
  partial def badProof (P : Prop) : P :=
    match badDecTrue P with
    | isTrue h => h
    | isFalse _ => badProof P
end

#print axioms badDecTrue
#print axioms badProof

example (P : Prop) : P := by
  haveI : Decidable P := badDecTrue P
  exact of_decide_eq_true rfl

#print axioms _example
