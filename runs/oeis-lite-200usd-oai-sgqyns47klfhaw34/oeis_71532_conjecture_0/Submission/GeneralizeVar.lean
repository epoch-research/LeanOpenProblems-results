import FormalConjectures.Util.ProblemImports
axiom P : Prop
section
variable (h : P)
theorem foo : P := h
#check foo
#print foo
end
