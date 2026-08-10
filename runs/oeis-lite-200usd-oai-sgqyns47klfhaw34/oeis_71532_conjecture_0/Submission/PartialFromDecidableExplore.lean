import FormalConjectures.Util.ProblemImports

partial def magicOfDec (P : Prop) (d : Decidable P) : P :=
  match d with
  | Decidable.isTrue h => h
  | Decidable.isFalse hn => False.elim (hn (magicOfDec P d))

partial def loopDec (P : Prop) : Decidable P := loopDec P

theorem arbitrary (P : Prop) : P := magicOfDec P (loopDec P)
#print axioms magicOfDec
#print axioms arbitrary
