import FormalConjectures.Util.ProblemImports
example : (∃ n : ℕ, n = 0) := by native_decide
example : ¬ (∃ n : ℕ, n < 0) := by native_decide
