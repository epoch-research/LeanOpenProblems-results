import FormalConjectures.Util.ProblemImports

section
variable (h : False)
include h
theorem bad : False := by exact h
#print bad
#print axioms bad
end
