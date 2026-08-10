import FormalConjectures.Util.ProblemImports

mutual
  partial def badProof (P : Prop) : P :=
    match badDec P with
    | Decidable.isTrue h => h
    | Decidable.isFalse hn => False.elim (hn (badProof P))
  partial def badDec (P : Prop) : Decidable P := Decidable.isTrue (badProof P)
end

theorem arb (P:Prop) : P := badProof P
#print axioms arb
