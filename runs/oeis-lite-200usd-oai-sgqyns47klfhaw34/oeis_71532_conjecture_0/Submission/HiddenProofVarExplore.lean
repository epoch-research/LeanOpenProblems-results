import FormalConjectures.Util.ProblemImports
axiom P : Prop
variable (h : P)
theorem foo : P := h
#print foo
#print axioms foo
