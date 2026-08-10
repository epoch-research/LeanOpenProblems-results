import FormalConjectures.Util.ProblemImports
set_option maxHeartbeats 0
set_option maxRecDepth 10000000

theorem count_test : Nat.count Nat.Prime 8165753 = 550171 := by
  decide
#print axioms count_test

theorem nth_test : Nat.nth Nat.Prime 550171 = 8165753 := by
  rw [← count_test]
  exact Nat.nth_count (by norm_num : Nat.Prime 8165753)
#print axioms nth_test
