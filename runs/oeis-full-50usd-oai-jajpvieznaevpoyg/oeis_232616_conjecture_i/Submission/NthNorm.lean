import FormalConjectures.Util.ProblemImports
set_option maxHeartbeats 20000000
set_option maxRecDepth 1000000
example : Nat.nth Nat.Prime 4 = 11 := by norm_num
example : Nat.nth Nat.Prime 10 = 31 := by norm_num
-- example : Nat.nth Nat.Prime 550171 = 8165753 := by norm_num
