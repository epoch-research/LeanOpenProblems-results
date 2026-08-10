import FormalConjectures.Util.ProblemImports
example : ∀ n : ℕ, n = n := by
  classical
  decide
#print axioms _example
