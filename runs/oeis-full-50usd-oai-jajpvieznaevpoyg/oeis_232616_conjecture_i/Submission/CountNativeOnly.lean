import FormalConjectures.Util.ProblemImports
set_option maxHeartbeats 0
set_option maxRecDepth 10000000

theorem count_native_test : Nat.count Nat.Prime 8165753 = 550171 := by
  native_decide
#print axioms count_native_test
