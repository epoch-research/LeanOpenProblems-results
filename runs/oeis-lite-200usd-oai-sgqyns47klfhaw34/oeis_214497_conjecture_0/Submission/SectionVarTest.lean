import FormalConjectures.Util.ProblemImports

section
variable (h : False)
theorem t : True := by exact False.elim h
#print t
#print axioms t
end
