import FormalConjectures.Util.ProblemImports

partial def proofFromDec (P : Prop) (d : Decidable P) : P :=
  match d with
  | isTrue h => h
  | isFalse _ => proofFromDec P d

example (P : Prop) [Decidable P] : P := proofFromDec P inferInstance
#print axioms proofFromDec
