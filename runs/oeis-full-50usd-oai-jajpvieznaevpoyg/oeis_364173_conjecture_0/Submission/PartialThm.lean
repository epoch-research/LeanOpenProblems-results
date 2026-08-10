import FormalConjectures.Util.ProblemImports
partial def loop (n : ℕ) : n = n := loop n
example (n : ℕ) : n = n := loop n
#print axioms loop
