import FormalConjectures.Util.ProblemImports
example : ∀ n : ℕ, n = n := by native_decide
example : ∀ n : ℕ, n + 0 = n := by decide
