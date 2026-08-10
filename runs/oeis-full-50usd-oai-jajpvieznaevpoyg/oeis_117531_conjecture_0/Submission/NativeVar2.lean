import FormalConjectures.Util.ProblemImports
example (n : Nat) : n < n+1 := by native_decide +revert
example : ∀ n : Nat, n < n+1 := by native_decide
example : ∀ n : Nat, n < n := by native_decide
