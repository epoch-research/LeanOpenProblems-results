import FormalConjectures.Util.ProblemImports
example (n : Nat) : ∃ k < n+1, k = n := by
  native_decide +revert
