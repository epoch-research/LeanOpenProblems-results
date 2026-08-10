import FormalConjectures.Util.ProblemImports

theorem my_choice (P : Prop) : P ∨ ¬P := Classical.em P
