import FormalConjectures.Util.ProblemImports
axiom P : Prop
section
variable (h : P)
include h
theorem foo : P := h
#check foo
#print foo
end
