import FormalConjectures.Util.ProblemImports
opaque h2 : Nat.Prime 2 := by norm_num
#print axioms h2
theorem t : Nat.Prime 2 := h2
#print axioms t
