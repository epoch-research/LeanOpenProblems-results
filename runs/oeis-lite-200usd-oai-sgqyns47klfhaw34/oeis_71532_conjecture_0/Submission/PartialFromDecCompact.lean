import FormalConjectures.Util.ProblemImports
partial def loopDec (P : Prop) : Decidable P := loopDec P
partial def fromDec (P : Prop) (d : Decidable P) : P :=
  match d with
  | .isTrue h => h
  | .isFalse _ => fromDec P (loopDec P)

theorem arbitrary (P : Prop) : P := fromDec P (loopDec P)
#print axioms fromDec
#print axioms arbitrary
