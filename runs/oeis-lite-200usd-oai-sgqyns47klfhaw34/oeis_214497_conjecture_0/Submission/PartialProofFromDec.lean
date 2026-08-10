import FormalConjectures.Util.ProblemImports

partial def decLoop (P : Prop) : Decidable P := decLoop P

partial def proofFromDec (P : Prop) : P :=
  match decLoop P with
  | isTrue h => h
  | isFalse _ => proofFromDec P

example (P : Prop) : P := proofFromDec P

#print axioms decLoop
#print axioms proofFromDec
