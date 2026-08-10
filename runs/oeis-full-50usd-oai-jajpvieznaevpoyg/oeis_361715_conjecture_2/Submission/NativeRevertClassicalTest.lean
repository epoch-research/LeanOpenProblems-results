import FormalConjectures.Util.ProblemImports
example (n : Nat) : n = n := by
  classical
  native_decide +revert
