import FormalConjectures.Util.ProblemImports

unsafe opaque my_helper (n : ℕ) : n = n + 1 := my_helper n

#print axioms my_helper
