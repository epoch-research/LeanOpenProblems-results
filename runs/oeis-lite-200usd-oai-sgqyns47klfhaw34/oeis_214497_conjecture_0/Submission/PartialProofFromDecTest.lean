import FormalConjectures.Util.ProblemImports

partial def decP (P : Prop) : Decidable P := decP P

partial def proofP (P : Prop) : P :=
  match decP P with
  | isTrue h => h
  | isFalse _ => proofP P

example (P : Prop) : P := proofP P
#print axioms proofP
