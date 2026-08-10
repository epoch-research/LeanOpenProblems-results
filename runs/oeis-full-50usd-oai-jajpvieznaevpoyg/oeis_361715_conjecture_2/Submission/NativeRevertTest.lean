import FormalConjectures.Util.ProblemImports
example (n : Nat) : n = n := by
  native_decide +revert
