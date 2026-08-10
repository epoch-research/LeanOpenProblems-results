import FormalConjectures.Util.ProblemImports

instance (P : Prop) : Nonempty (P ∨ ¬P) := Nonempty.intro (Classical.em P)

partial def my_partial_em (P : Prop) : P ∨ ¬P :=
  my_partial_em P

theorem my_em (P : Prop) : P ∨ ¬P :=
  my_partial_em P


#print axioms my_partial_em
#print axioms my_em
