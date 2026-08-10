import FormalConjectures.Util.ProblemImports
set_option maxRecDepth 100000
example : Nat.count Nat.Prime 5309 = 703 := by decide
example : Nat.nth Nat.Prime 703 = 5309 := by
  rw [← (show Nat.count Nat.Prime 5309 = 703 by decide)]
  exact Nat.nth_count (by norm_num : Nat.Prime 5309)
