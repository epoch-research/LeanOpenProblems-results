import FormalConjectures.Util.ProblemImports

opaque my_theorem : ∀ (x : ℕ), ∃ (i : ℕ), ∀ (n : ℕ), i < n → a n > x

#print axioms my_theorem
