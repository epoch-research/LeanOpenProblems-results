import FormalConjectures.Util.ProblemImports
example : ∀ n : ℕ, n = n := by
  native_decide
#print axioms _example
