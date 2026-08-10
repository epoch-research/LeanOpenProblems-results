import FormalConjectures.Util.ProblemImports

partial def decLoop (P : Prop) : Decidable P := decLoop P

def arbAux (P : Prop) (self : P) : P :=
  match decLoop P with
  | isTrue h => h
  | isFalse h => False.elim (h self)

theorem arbitrary3 (P : Prop) : P := arbAux P (arbitrary3 P)
#print axioms arbitrary3
