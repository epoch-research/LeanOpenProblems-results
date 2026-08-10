import FormalConjectures.Util.ProblemImports
example (n : ℕ) : n = n := by
  native_decide +revert
#print axioms _example
