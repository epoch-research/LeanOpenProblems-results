import FormalConjectures.Util.ProblemImports
partial def bad : ∀ n : ℕ, n = n := fun n => bad n
example (n : ℕ) : n = n := bad n
#print axioms bad
#print axioms PartialProof._example
