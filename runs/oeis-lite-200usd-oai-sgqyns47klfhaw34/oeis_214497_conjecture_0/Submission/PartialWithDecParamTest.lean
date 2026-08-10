import FormalConjectures.Util.ProblemImports

partial def extractFromDec (P : Prop) (d : Decidable P) : P :=
  match d with
  | Decidable.isTrue h => h
  | Decidable.isFalse _ => extractFromDec P d

#print axioms extractFromDec
example (P : Prop) : P := extractFromDec P (Classical.dec P)
#print axioms _example
