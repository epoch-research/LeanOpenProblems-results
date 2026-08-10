import FormalConjectures.Util.ProblemImports

section
variable (h : False)
theorem t : True := by
  exact False.elim h
#check t
#print t
end
