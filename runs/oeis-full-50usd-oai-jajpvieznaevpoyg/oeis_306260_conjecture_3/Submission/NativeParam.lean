import FormalConjectures.Util.ProblemImports
example (n : ℕ) : n = n := by native_decide +revert
example (n : ℕ) : ∃ m ≤ n, m = n := by native_decide +revert
