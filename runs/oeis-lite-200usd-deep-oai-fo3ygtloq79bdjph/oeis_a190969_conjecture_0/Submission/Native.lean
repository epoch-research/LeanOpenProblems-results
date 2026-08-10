import FormalConjectures.Util.ProblemImports
example (n : ℕ) : n = n := by native_decide +revert
example (n : ℕ) : n + 1 ≠ 0 := by native_decide +revert
