import FormalConjectures.Util.ProblemImports

example (n : ℕ) : n = n := by decide +revert
example (n : ℕ) : n + 0 = n := by decide +revert
example (n m : ℕ) : Decidable (n = m) := inferInstance
