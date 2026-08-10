import FormalConjectures.Util.ProblemImports

partial def weirdDec (P : Prop) : Decidable P :=
  match weirdDec P with
  | isTrue h => isTrue h
  | isFalse hn => isFalse hn

partial def extract (P : Prop) : P :=
  match weirdDec P with
  | isTrue h => h
  | isFalse hn => False.elim (hn (extract P))

example : False := extract False
#print extract
#print axioms extract
#print axioms _example
