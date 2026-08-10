import Mathlib
example : ∀ n : Nat, n = n := by
  classical
  native_decide
example : ∀ n : Nat, n < n+1 := by
  classical
  native_decide
example (n : Nat) : n < n+1 := by
  classical
  native_decide
