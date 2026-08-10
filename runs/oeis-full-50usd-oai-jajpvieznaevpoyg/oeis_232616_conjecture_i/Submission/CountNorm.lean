import FormalConjectures.Util.ProblemImports
set_option maxHeartbeats 0
set_option maxRecDepth 10000000

theorem count_norm_test : Nat.count Nat.Prime 8165753 = 550171 := by
  norm_num [Nat.count]
#print axioms count_norm_test
