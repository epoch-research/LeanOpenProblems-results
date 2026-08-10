import FormalConjectures.Util.ProblemImports
partial def f (n : ℕ) : ℕ := f n
#check f
#print axioms f
example (n : ℕ) : ℕ := f n
