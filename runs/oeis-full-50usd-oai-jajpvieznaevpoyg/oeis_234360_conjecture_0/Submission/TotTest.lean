import FormalConjectures.Util.ProblemImports

open Nat Finset

example : Nat.totient 9 = 6 := by norm_num [Nat.totient]
example : Nat.totient 9 = 6 := by native_decide
example : Nat.totient 9 = 6 := by decide
example : Nat.totient 9 = 6 := by simp [Nat.totient]
