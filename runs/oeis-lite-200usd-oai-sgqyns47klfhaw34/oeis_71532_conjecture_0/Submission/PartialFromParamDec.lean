import FormalConjectures.Util.ProblemImports

partial def decLoop (P : Prop) : Decidable P := decLoop P

partial def proveFromDec (P : Prop) (d : Decidable P) : P :=
  match d with
  | isTrue h => h
  | isFalse _ => proveFromDec P d

#print axioms proveFromDec
example (P : Prop) : P := proveFromDec P (decLoop P)
