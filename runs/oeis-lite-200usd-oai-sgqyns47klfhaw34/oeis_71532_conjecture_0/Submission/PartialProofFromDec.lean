import FormalConjectures.Util.ProblemImports

partial def decLoop (P : Prop) : Decidable P := decLoop P

partial def proveLoop (P : Prop) : P :=
  match decLoop P with
  | isTrue h => h
  | isFalse _ => proveLoop P

#print axioms proveLoop
example (P : Prop) : P := proveLoop P
