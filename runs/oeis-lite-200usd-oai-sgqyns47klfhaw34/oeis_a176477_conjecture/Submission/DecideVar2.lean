import FormalConjectures.Util.ProblemImports
example (n : Nat) : n = n := by
  classical
  native_decide +revert
example (n : Nat) : n ≥ 1 → n > 0 := by
  classical
  native_decide +revert
