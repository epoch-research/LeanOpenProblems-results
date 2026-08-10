import FormalConjectures.Util.ProblemImports

open Nat

theorem test_native : 1 + 1 = 2 := by
  native_decide

#print axioms test_native
