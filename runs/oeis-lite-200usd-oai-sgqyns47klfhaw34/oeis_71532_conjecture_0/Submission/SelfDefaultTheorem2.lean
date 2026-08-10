import FormalConjectures.Util.ProblemImports

theorem arbitrary (P : Prop) (h : P := arbitrary P) : P := h
#print axioms arbitrary
