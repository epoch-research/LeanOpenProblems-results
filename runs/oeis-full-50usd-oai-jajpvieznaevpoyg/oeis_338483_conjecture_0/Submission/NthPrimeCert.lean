import FormalConjectures.Util.ProblemImports
open Finset Nat Set
example : Nat.nth Nat.Prime 664579 = 10000019 := by native_decide
example : Nat.primeCounting' 10000019 = 664579 := by
  rw [← Nat.primeCounting'_nth_eq 664579]
  congr
  native_decide
