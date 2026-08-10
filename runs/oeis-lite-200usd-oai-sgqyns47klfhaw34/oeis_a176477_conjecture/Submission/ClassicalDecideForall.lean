import FormalConjectures.Util.ProblemImports
example : (∀ n : ℕ, n = n) := by
  classical
  decide
example : (∀ n : ℕ, False) := by
  classical
  decide
