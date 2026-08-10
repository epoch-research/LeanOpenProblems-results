import FormalConjectures.Util.ProblemImports

section
variable (h : False)
include h
theorem t1 : True := by exact False.elim h
#print t1
end

section
variable [Subsingleton Nat]
theorem t2 (x y : Nat) : x = y := by exact Subsingleton.elim _ _
#print t2
end
