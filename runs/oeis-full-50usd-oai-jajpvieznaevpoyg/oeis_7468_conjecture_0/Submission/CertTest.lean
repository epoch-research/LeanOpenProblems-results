import FormalConjectures.Util.ProblemImports

example : Nat.count Nat.Prime 5309 = 703 := by native_decide
example : Nat.nth Nat.Prime 703 = 5309 := by
  rw [← (show Nat.count Nat.Prime 5309 = 703 by native_decide)]
  exact Nat.nth_count (by native_decide : Nat.Prime 5309)
