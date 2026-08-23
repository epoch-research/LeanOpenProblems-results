import FormalConjectures.Util.ProblemImports
open Finset Nat
example : Nat.count Nat.Prime 13 = 5 := by decide
example : Nat.nth Nat.Prime 5 = 13 := by
  rw [← show Nat.count Nat.Prime 13 = 5 by decide]
  exact Nat.nth_count (by norm_num)
example : Nat.nth Nat.Prime 6 = 17 := by
  rw [← show Nat.count Nat.Prime 17 = 6 by decide]
  exact Nat.nth_count (by norm_num)
example : Nat.nth Nat.Prime 7 = 19 := by
  rw [← show Nat.count Nat.Prime 19 = 7 by decide]
  exact Nat.nth_count (by norm_num)
example : Nat.nth Nat.Prime 8 = 23 := by
  rw [← show Nat.count Nat.Prime 23 = 8 by decide]
  exact Nat.nth_count (by norm_num)
