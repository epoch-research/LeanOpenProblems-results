import FormalConjectures.Util.ProblemImports
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option exponentiation.threshold 30000
example : 2^29400 % 137543 = 1 := by native_decide
example : 2^29400 % 137543 = 1 := by decide
