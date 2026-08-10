import FormalConjectures.Util.ProblemImports

open Nat

theorem test_decide_normal : totient 10 = 4 := by
  decide

#print axioms test_decide_normal
