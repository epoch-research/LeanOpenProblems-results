import FormalConjectures.Util.ProblemImports
set_option maxHeartbeats 2000000

example : Nat.nth Nat.Prime 550171 = 8165753 := by
  native_decide

#print axioms _example
