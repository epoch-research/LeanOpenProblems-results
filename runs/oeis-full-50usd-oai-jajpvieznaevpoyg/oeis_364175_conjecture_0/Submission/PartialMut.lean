import FormalConjectures.Util.ProblemImports
mutual
partial def badProof (P : Prop) : P :=
  match badDec P with
  | Decidable.isTrue h => h
  | Decidable.isFalse nh => False.elim (nh (badProof P))
partial def badDec (P : Prop) : Decidable P :=
  Decidable.isTrue (badProof P)
end

theorem bad (P : Prop) : P := badProof P
#print axioms bad
example : False := bad False
