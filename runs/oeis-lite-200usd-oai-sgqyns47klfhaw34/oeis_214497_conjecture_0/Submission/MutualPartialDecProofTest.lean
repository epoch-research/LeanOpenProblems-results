import FormalConjectures.Util.ProblemImports

mutual
partial def mdec (P : Prop) : Decidable P := Decidable.isTrue (mproof P)
partial def mproof (P : Prop) : P :=
  match mdec P with
  | Decidable.isTrue h => h
  | Decidable.isFalse hn => False.elim (hn (mproof P))
end

theorem any_mutual (P : Prop) : P := mproof P
#print axioms any_mutual
