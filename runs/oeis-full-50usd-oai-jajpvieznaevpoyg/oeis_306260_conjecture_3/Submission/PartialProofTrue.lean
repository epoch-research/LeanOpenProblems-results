import FormalConjectures.Util.ProblemImports
partial def pfTrue (n : ℕ) : n = n := pfTrue n
example (n : ℕ) : n = n := pfTrue n
#print axioms pfTrue
