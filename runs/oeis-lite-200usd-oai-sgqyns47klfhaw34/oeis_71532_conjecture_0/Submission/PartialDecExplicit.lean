import FormalConjectures.Util.ProblemImports

partial def loopDec (P : Prop) : Decidable P := loopDec P

partial def getFromDec (P : Prop) (d : Decidable P) : P :=
  match d with
  | isTrue h => h
  | isFalse _ => getFromDec P (loopDec P)

partial def getFromDecDefault (P : Prop) (d : Decidable P := loopDec P) : P :=
  match d with
  | isTrue h => h
  | isFalse _ => getFromDecDefault P (loopDec P)

#print getFromDec
#print getFromDecDefault
#print axioms getFromDec
#print axioms getFromDecDefault

example (P : Prop) : P := getFromDec P (loopDec P)
#print axioms _example
