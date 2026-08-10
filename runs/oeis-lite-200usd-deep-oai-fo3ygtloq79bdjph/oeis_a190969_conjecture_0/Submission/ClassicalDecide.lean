import FormalConjectures.Util.ProblemImports
example : ∀ n : ℕ, n = n := by
  classical
  decide
example : False := by
  classical
  decide
