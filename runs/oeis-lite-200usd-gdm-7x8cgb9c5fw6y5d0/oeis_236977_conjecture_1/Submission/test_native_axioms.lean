import FormalConjectures.Util.ProblemImports

open Nat

set_option native_decide true

theorem test_native : totient 1000 = 400 := by
  native_decide

#print axioms test_native
