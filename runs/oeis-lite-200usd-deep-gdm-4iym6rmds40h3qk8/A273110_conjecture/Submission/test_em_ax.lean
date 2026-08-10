import FormalConjectures.Util.ProblemImports

theorem my_choice_ax (P : Prop) : P ∨ ¬P := Classical.em P

#print axioms my_choice_ax
