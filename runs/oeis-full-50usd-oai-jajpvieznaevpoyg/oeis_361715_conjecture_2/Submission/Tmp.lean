import FormalConjectures.Util.ProblemImports

example (n : ℕ) : n = n := by native_decide +revert
example (n : ℕ) : n + 0 = n := by native_decide +revert
