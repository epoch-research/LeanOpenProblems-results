import FormalConjectures.Util.ProblemImports
set_option maxHeartbeats 0
set_option maxRecDepth 10000000
example : Nat.nth Nat.Prime (550172 - 1) = 8165753 := by norm_num
