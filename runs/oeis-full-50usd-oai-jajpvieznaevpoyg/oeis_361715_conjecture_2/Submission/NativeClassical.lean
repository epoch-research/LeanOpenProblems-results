import FormalConjectures.Util.ProblemImports

example (n : ℕ) : n = n := by
  classical
  native_decide +revert

example (n : ℕ) : n + 0 = n := by
  classical
  native_decide +revert
