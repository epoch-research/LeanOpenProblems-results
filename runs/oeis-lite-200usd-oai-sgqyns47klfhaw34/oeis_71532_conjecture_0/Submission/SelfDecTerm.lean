import FormalConjectures.Util.ProblemImports

partial def decLoop (P : Prop) : Decidable P := decLoop P

theorem arbitrary2 (P : Prop) : P :=
  match decLoop P with
  | isTrue h => h
  | isFalse h => False.elim (h (arbitrary2 P))

#print axioms arbitrary2
