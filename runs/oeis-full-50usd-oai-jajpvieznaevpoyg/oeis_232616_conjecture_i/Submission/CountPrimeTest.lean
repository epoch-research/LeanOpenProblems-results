import FormalConjectures.Util.ProblemImports
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
#check Nat.count
example : Nat.count Nat.Prime 31 = 10 := by
  native_decide
example : Nat.count Nat.Prime 31 = 10 := by
  decide
